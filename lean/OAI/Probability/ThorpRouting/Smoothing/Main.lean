import Mathlib
import OAI.Probability.ThorpRouting.Smoothing.ParallelFreshPre

namespace OAI

namespace ThorpNine.Smoothing

namespace Thorp

theorem palindrome_family_mgf (L n d : ℕ) (hL : 0 < L) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (X : SwitchIndex d → Bool) (q : ℝ) (hq : 1 ≤ q)
    (hlog : Real.log q ≤ 1/250) :
    finiteMean (fun Y => q^(palindromeFamilyCost L n d e (Y,X))) ≤
      Real.exp (Fintype.card ι * (68*∑ j ∈ Finset.range n,
        Real.exp (-((L*4^j:ℕ):ℝ)/64))) := by
  induction n with
  | zero => simp only [palindromeFamilyCost,Finset.range_zero,Finset.sum_empty,pow_zero,
      finiteMean_const,mul_zero,Real.exp_zero,le_refl]
  | succ n ih =>
    let l := L*4^n
    have hl : 0 < l := Nat.mul_pos hL (pow_pos (by decide) _)
    have hs : 2*familyEnd L n ≤ l := familyEnd_two L n
    have hc : ∀ Y, palindromeFamilyCost L (n+1) d e (Y,X) =
        palindromeFamilyCost L n d e (Y,X)+palindromeSlabCost l d e (Y,X) := by
      intro Y
      exact Finset.sum_range_succ _ _
    have hm : finiteMean (fun Y => q^(palindromeFamilyCost L (n+1) d e (Y,X))) ≤
        finiteMean (fun Y => q^(palindromeFamilyCost L n d e (Y,X))) *
          Real.exp (Fintype.card ι*(68*Real.exp (-(l:ℝ)/64))) := by
      by_cases hld : l ≤ d
      · simp_rw [hc,pow_add]
        exact palindrome_slab_adapted_mul_le d (familyEnd L n) l (by omega) hl hs e X _
          (fun _ => pow_nonneg (by linarith) _)
          (layerAdapted_comp (palindromeFamilyCost_adapted L n d e X) (fun c => q^c))
          q hq hlog
      · simp_rw [hc,palindromeSlabCost_gt l d (by omega) e,Nat.add_zero]
        exact le_mul_of_one_le_right
          (finiteMean_nonneg (fun _ => pow_nonneg (by linarith) _))
          (Real.one_le_exp_iff.mpr (by positivity))
    refine (hm.trans (mul_le_mul_of_nonneg_right ih (Real.exp_nonneg _))).trans_eq ?_
    rw [←Real.exp_add,Finset.sum_range_succ]
    congr 1
    dsimp [l]
    ring

lemma pow_four_ge (j : ℕ) : j+1 ≤ 4^j := by
  induction j with
  | zero => norm_num
  | succ j ih => rw [pow_succ]; omega

lemma sum_family_decay (L n : ℕ) (hL : 0 < L) :
    (∑ j ∈ Finset.range n, Real.exp (-((L*4^j:ℕ):ℝ)/64)) ≤
      Real.exp (-(L:ℝ)/64)/(1-Real.exp (-(1:ℝ)/64)) := by
  let r := Real.exp (-(1:ℝ)/64)
  have hr : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hg : (∑ j ∈ Finset.range n, r^j) ≤ 1/(1-r) := by
    apply (le_div_iff₀ (by linarith : (0:ℝ)<1-r)).mpr
    have hh := geom_sum_mul r n
    nlinarith [pow_nonneg (le_of_lt hr) n]
  calc
    _ ≤ ∑ j ∈ Finset.range n, Real.exp (-(L:ℝ)/64)*r^j := by
      apply Finset.sum_le_sum
      intro j _
      have hj := pow_four_ge j
      have hlj : L+j ≤ L*4^j := by nlinarith
      have hlj' : (L:ℝ)+j ≤ (L*4^j:ℕ) := by exact_mod_cast hlj
      rw [←Real.exp_nat_mul,←Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (-(L:ℝ)/64)*(∑ j ∈ Finset.range n, r^j) := by rw [Finset.mul_sum]
    _ ≤ Real.exp (-(L:ℝ)/64)*(1/(1-r)) :=
      mul_le_mul_of_nonneg_left hg (Real.exp_nonneg _)
    _ = _ := by ring


lemma palindromeLevelCost_step_add (t d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card (d+1)) (ω : BenesCoins (d+1)) :
    palindromeLevelCost t (d+1) e ω =
      let σ := benesStepEquiv d ω
      let x := e.trans (headTailEquiv d).toEmbedding
      let c := PairRouting.colors x σ.2.1
      let hc := PairRouting.colors_compatible x σ.2.1
      (if t = d+1 then PairRouting.alternatingCycles (PairRouting.switchedEmbedding x σ.2.1)
          (fun b => palindromePerm d (if b then σ.1.2 else σ.1.1)) else 0) +
        palindromeLevelCost t d (PairRouting.childEmbedding x c hc false) σ.1.1 +
        palindromeLevelCost t d (PairRouting.childEmbedding x c hc true) σ.1.2 := by
  classical
  rw [palindromeLevelCost]
  dsimp only
  split_ifs with h
  · simp only [palindromeLevelCost_gt t d (by omega),Nat.add_zero]
  · simp only [Nat.zero_add]

lemma palindromeLowCost_sum (H d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (ω : BenesCoins d) :
    palindromeLowCost H d e ω = ∑ i ∈ Finset.range H, palindromeLevelCost (i+1) d e ω := by
  classical
  induction d generalizing ι with
  | zero => simp only [palindromeLowCost,palindromeLevelCost,Finset.sum_const_zero]
  | succ d ih =>
    rw [palindromeLowCost]
    simp only [palindromeLevelCost_step_add,Finset.sum_add_distrib]
    rw [←ih,←ih]
    congr 2
    simp only [Nat.add_right_cancel_iff,Finset.sum_ite_eq',Finset.mem_range,Nat.succ_le_iff]

lemma palindromeLowCost_slab (L d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (ω : BenesCoins d) :
    palindromeLowCost L d e ω + palindromeSlabCost L d e ω = palindromeLowCost (2*L) d e ω := by
  rw [palindromeLowCost_sum,palindromeLowCost_sum,show 2*L=L+L by omega,Finset.sum_range_add]
  congr 1
  exact Fin.sum_univ_eq_sum_range (fun i => palindromeLevelCost (L+i+1) d e ω) L

lemma palindromeCost_family (L n d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (ω : BenesCoins d) :
    palindromeLowCost L d e ω + palindromeFamilyCost L n d e ω +
      palindromeFamilyCost (2*L) n d e ω = palindromeLowCost (L*4^n) d e ω := by
  induction n with
  | zero => simp only [palindromeFamilyCost,Finset.range_zero,Finset.sum_empty,Nat.add_zero,
      pow_zero,mul_one]
  | succ n ih =>
    have he : (2*L)*4^n = 2*(L*4^n) := by ring
    have he' : L*4^(n+1) = 2*(2*(L*4^n)) := by rw [pow_succ]; ring
    simp only [palindromeFamilyCost,Finset.sum_range_succ] at ih ⊢
    rw [he,he',←palindromeLowCost_slab,←palindromeLowCost_slab,←ih]
    omega


lemma finiteMean_mul_sq_le {Ω : Type*} [Fintype Ω] (f g : Ω → ℝ) :
    (finiteMean (fun ω => f ω*g ω))^2 ≤ finiteMean (fun ω => (f ω)^2)*finiteMean (fun ω => (g ω)^2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g
  simp only [finiteMean,div_pow,div_mul_div_comm,←pow_two]
  exact div_le_div_of_nonneg_right h (sq_nonneg _)

lemma finiteMean_mul_exp_le {Ω : Type*} [Fintype Ω] (f g : Ω → ℝ) (A B : ℝ)
    (hf : finiteMean (fun ω => (f ω)^2) ≤ Real.exp A)
    (hg : finiteMean (fun ω => (g ω)^2) ≤ Real.exp B) :
    finiteMean (fun ω => f ω*g ω) ≤ Real.exp ((A+B)/2) := by
  have hc := finiteMean_mul_sq_le f g
  have hn : 0 ≤ finiteMean (fun ω => (g ω)^2) := finiteMean_nonneg (fun _ => sq_nonneg _)
  have hu := mul_le_mul hf hg hn (Real.exp_nonneg _)
  have he : Real.exp A*Real.exp B = (Real.exp ((A+B)/2))^2 := by
    rw [←Real.exp_add,←Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [he] at hu
  have hh := hc.trans hu
  have hep := Real.exp_pos ((A+B)/2)
  nlinarith


noncomputable def heightDecay (H : ℕ) : ℝ :=
  68*Real.exp (-(H:ℝ)/64)/(1-Real.exp (-(1:ℝ)/64))

lemma heightDecay_nonneg (H : ℕ) : 0 ≤ heightDecay H := by
  have h : Real.exp (-(1:ℝ)/64) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  apply div_nonneg (by positivity) (by linarith)

lemma heightDecay_antitone : Antitone heightDecay := by
  intro L H h
  have hden : 0 ≤ 1-Real.exp (-(1:ℝ)/64) := by
    have h := Real.exp_lt_one_iff.mpr (by norm_num : -(1:ℝ)/64 < 0)
    linarith
  apply div_le_div_of_nonneg_right _ hden
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  have h' : (L:ℝ) ≤ H := by exact_mod_cast h
  linarith

lemma palindrome_family_mgf_decay (L n d : ℕ) (hL : 0 < L) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (X : SwitchIndex d → Bool) (q : ℝ) (hq : 1 ≤ q)
    (hlog : Real.log q ≤ 1/250) :
    finiteMean (fun Y => q^(palindromeFamilyCost L n d e (Y,X))) ≤
      Real.exp (Fintype.card ι*heightDecay L) := by
  apply (palindrome_family_mgf L n d hL e X q hq hlog).trans
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  have h := mul_le_mul_of_nonneg_left (sum_family_decay L n hL) (by norm_num : (0:ℝ)≤68)
  simpa only [heightDecay,mul_div_assoc] using h

theorem palindrome_high_mgf (H n d : ℕ) (hH : 0 < H) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (X : SwitchIndex d → Bool) (q : ℝ) (hq : 1 ≤ q)
    (hlog : Real.log q ≤ 1/500) :
    finiteMean (fun Y => q^(palindromeFamilyCost H n d e (Y,X)+
      palindromeFamilyCost (2*H) n d e (Y,X))) ≤ Real.exp (Fintype.card ι*heightDecay H) := by
  have hq2 := one_le_pow₀ (n:=2) hq
  have hlog2 : Real.log (q^2) ≤ 1/250 := by rw [Real.log_pow]; norm_num; linarith
  have h₀ := palindrome_family_mgf_decay H n d hH e X (q^2) hq2 hlog2
  have h₁ := palindrome_family_mgf_decay (2*H) n d (by omega) e X (q^2) hq2 hlog2
  have h₁' := h₁.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
    (heightDecay_antitone (show H ≤ 2*H by omega)) (Nat.cast_nonneg _)))
  have hh := finiteMean_mul_exp_le (fun Y => q^(palindromeFamilyCost H n d e (Y,X)))
    (fun Y => q^(palindromeFamilyCost (2*H) n d e (Y,X)))
    (Fintype.card ι*heightDecay H) (Fintype.card ι*heightDecay H)
    (by simpa only [pow_right_comm] using h₀) (by simpa only [pow_right_comm] using h₁')
  simpa only [←pow_add,add_self_div_two] using hh

lemma palindrome_high_full_mgf (H n d : ℕ) (hH : 0 < H) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (q : ℝ) (hq : 1 ≤ q) (hlog : Real.log q ≤ 1/500) :
    finiteMean (fun ω : BenesCoins d => q^(palindromeFamilyCost H n d e ω+
      palindromeFamilyCost (2*H) n d e ω)) ≤ Real.exp (Fintype.card ι*heightDecay H) := by
  rw [finiteMean_prod,finiteMean_comm]
  calc
    _ ≤ finiteMean (fun _X : SwitchIndex d → Bool => Real.exp (Fintype.card ι*heightDecay H)) := by
      apply finiteMean_mono
      intro X
      exact palindrome_high_mgf H n d hH e X q hq hlog
    _ = _ := finiteMean_const _

theorem palindrome_cost_mgf_cutoff (r H : ℕ) (hH : 0 < H) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card (H+r)) (q : ℝ) (hq : 1 ≤ q) (hlog : Real.log q ≤ 1/1000)
    (hr : (2:ℝ)^H*((Fintype.card ι/(2:ℝ)^(H+r))*(q^2)^H) ≤ 1/2) :
    finiteMean (fun ω : BenesCoins (H+r) => q^(palindromeCost (H+r) e ω)) ≤
      Real.exp (((2:ℝ)^r*(2*((2:ℝ)^H*((Fintype.card ι/(2:ℝ)^(H+r))*(q^2)^H))^2)+
        Fintype.card ι*heightDecay H)/2) := by
  let d := H+r
  have hd : d ≤ H*4^d := by
    have hh := pow_four_ge d
    nlinarith
  have hcost (ω : BenesCoins d) : palindromeCost d e ω = palindromeLowCost H d e ω+
      (palindromeFamilyCost H d d e ω+palindromeFamilyCost (2*H) d d e ω) := by
    have hh := palindromeCost_family H d d e ω
    rw [palindromeLowCost_eq _ _ hd] at hh
    simpa only [Nat.add_assoc] using hh.symm
  have hq2 := one_le_pow₀ (n:=2) hq
  have hlog2 : Real.log (q^2) ≤ 1/500 := by rw [Real.log_pow]; norm_num; linarith
  have hlow := palindrome_low_mgf r H e (q^2) hq2 hr
  have hhigh := palindrome_high_full_mgf H d d hH e (q^2) hq2 hlog2
  have hh := finiteMean_mul_exp_le (fun ω : BenesCoins d => q^(palindromeLowCost H d e ω))
    (fun ω : BenesCoins d => q^(palindromeFamilyCost H d d e ω+palindromeFamilyCost (2*H) d d e ω))
    _ _ (by simpa only [pow_right_comm] using hlow) (by simpa only [pow_right_comm] using hhigh)
  change finiteMean (fun ω : BenesCoins d => q^(palindromeCost d e ω)) ≤ _
  simpa only [hcost,pow_add,pow_right_comm] using hh


lemma cutoffMass_le (H d : ℕ) {ι : Type*} [Fintype ι] (e : ι ↪ Card d) (ω : BenesCoins d) :
    cutoffMass H d e ω ≤ Fintype.card ι := by
  classical
  induction d generalizing ι with
  | zero => exact Nat.zero_le _
  | succ d ih =>
    rw [cutoffMass]
    split_ifs
    · exact crowdedMass_le _
    · exact (Nat.add_le_add (ih _ _) (ih _ _)).trans_eq (PairRouting.color_card_add _)

lemma palindromeLowCost_le (H d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (ω : BenesCoins d) : palindromeLowCost H d e ω ≤ H*Fintype.card ι :=
  (palindromeLowCost_le_cutoff H d e ω).trans (Nat.mul_le_mul_left H (cutoffMass_le H d e ω))

theorem palindrome_cost_mgf_coarse (d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (q : ℝ) (hq : 1 ≤ q) (hlog : Real.log q ≤ 1/1000) :
    finiteMean (fun ω : BenesCoins d => q^(palindromeCost d e ω)) ≤
      Real.exp (Fintype.card ι*(1+heightDecay 1)) := by
  have hd : d ≤ 1*4^d := by have hh := pow_four_ge d; omega
  have hcost (ω : BenesCoins d) : palindromeCost d e ω = palindromeLowCost 1 d e ω+
      (palindromeFamilyCost 1 d d e ω+palindromeFamilyCost 2 d d e ω) := by
    have hh := palindromeCost_family 1 d d e ω
    rw [palindromeLowCost_eq _ _ hd] at hh
    simpa only [Nat.add_assoc] using hh.symm
  have hq2 := one_le_pow₀ (n:=2) hq
  have hlog2 : Real.log (q^2) ≤ 1/500 := by rw [Real.log_pow]; norm_num; linarith
  have hlow : finiteMean (fun ω : BenesCoins d => (q^2)^(palindromeLowCost 1 d e ω)) ≤
      Real.exp (Fintype.card ι) := by
    calc
      _ ≤ finiteMean (fun _ω : BenesCoins d => (q^2)^(Fintype.card ι)) := by
        apply finiteMean_mono
        intro ω
        apply pow_le_pow_right₀ hq2
        simpa only [one_mul] using palindromeLowCost_le 1 d e ω
      _ = (q^2)^(Fintype.card ι) := finiteMean_const _
      _ = Real.exp (Fintype.card ι * Real.log (q^2)) := by
        rw [Real.exp_nat_mul,Real.exp_log (by positivity : 0<q^2)]
      _ ≤ _ := Real.exp_le_exp.mpr (by
        have hh := mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg (Fintype.card ι) : (0:ℝ)≤_)
        nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card ι)])
  have hhigh := palindrome_high_full_mgf 1 d d (by decide) e (q^2) hq2 hlog2
  have hh := finiteMean_mul_exp_le (fun ω : BenesCoins d => q^(palindromeLowCost 1 d e ω))
    (fun ω : BenesCoins d => q^(palindromeFamilyCost 1 d d e ω+palindromeFamilyCost 2 d d e ω))
    (Fintype.card ι) (Fintype.card ι*heightDecay 1)
    (by simpa only [pow_right_comm] using hlow) (by simpa only [pow_right_comm] using hhigh)
  simp only [←pow_add,←hcost] at hh
  apply hh.trans (Real.exp_le_exp.mpr _)
  have hk : (0:ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have hD := heightDecay_nonneg 1
  nlinarith

noncomputable def momentBase : ℝ := (2:ℝ)^(1/1000:ℝ)

lemma momentBase_one_le : 1 ≤ momentBase := by
  exact Real.one_le_rpow (by norm_num) (by norm_num)

lemma momentBase_log : Real.log momentBase ≤ 1/1000 := by
  rw [momentBase,Real.log_rpow (by norm_num)]
  have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  norm_num at hh ⊢
  linarith

lemma momentBase_pow (c : ℕ) : momentBase^c = (2:ℝ)^((c:ℝ)*(1/1000:ℝ)) := by
  rw [mul_comm,Real.rpow_mul_natCast (by norm_num)]
  rfl

lemma palindromeRowMoment_le_cost (d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) :
    palindromeRowMoment d e (1/1000) ≤
      finiteMean (fun ω : BenesCoins d => momentBase^(palindromeCost d e ω)) := by
  have hn : (0:ℝ) < ((2^d:ℕ):ℝ)^(Fintype.card ι) := by positivity
  have hn0 : (0:ℝ) ≤ ((2^d).descFactorial (Fintype.card ι):ℝ) /
      ((2^d:ℕ):ℝ)^(Fintype.card ι) := by positivity
  have hn1 : ((2^d).descFactorial (Fintype.card ι):ℝ) /
      ((2^d:ℕ):ℝ)^(Fintype.card ι) ≤ 1 := by
    apply (div_le_one hn).mpr
    exact_mod_cast Nat.descFactorial_le_pow (2^d) (Fintype.card ι)
  have hpow := Real.rpow_le_one hn0 hn1 (by norm_num : (0:ℝ)≤1/1000)
  have hm := palindrome_row_density_moment d e (1/1000) (by norm_num)
  simp_rw [←momentBase_pow] at hm
  exact hm.trans (mul_le_of_le_one_left (finiteMean_nonneg (fun _ =>
    pow_nonneg (le_trans (by norm_num) momentBase_one_le) _)) hpow)

theorem palindrome_row_moment_coarse (d : ℕ) {ι : Type*} [Fintype ι] (e : ι ↪ Card d) :
    palindromeRowMoment d e (1/1000) ≤ Real.exp (Fintype.card ι*(1+heightDecay 1)) :=
  (palindromeRowMoment_le_cost d e).trans
    (palindrome_cost_mgf_coarse d e momentBase momentBase_one_le momentBase_log)


noncomputable def densityCutoff (p : ℝ) : ℕ := ⌊-Real.log p/(4*Real.log 2)⌋₊

lemma log_small_density {p : ℝ} (hp : 0 < p) (hs : p ≤ 1/256) :
    Real.log p ≤ -8*Real.log 2 := by
  have he : Real.log (1/256:ℝ) = -8*Real.log 2 := by
    rw [show (1/256:ℝ) = 1/2^8 by norm_num,
      Real.log_div (by norm_num) (by positivity),Real.log_one,Real.log_pow]
    ring
  exact (Real.log_le_log hp hs).trans_eq he

lemma densityCutoff_bounds {p : ℝ} (hp : 0 < p) (hs : p ≤ 1/256) :
    0 < densityCutoff p ∧
    (densityCutoff p:ℝ)*(4*Real.log 2) ≤ -Real.log p ∧
    -Real.log p < ((densityCutoff p:ℝ)+1)*(4*Real.log 2) := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hd : 0 < 4*Real.log 2 := by positivity
  have hh := log_small_density hp hs
  have hx : 1 ≤ -Real.log p/(4*Real.log 2) := by
    apply (le_div_iff₀ hd).mpr
    nlinarith
  refine ⟨Nat.floor_pos.mpr hx,?_,?_⟩
  · exact (le_div_iff₀ hd).mp (Nat.floor_le (by linarith : 0 ≤ -Real.log p/(4*Real.log 2)))
  · exact (div_lt_iff₀ hd).mp (Nat.lt_floor_add_one (-Real.log p/(4*Real.log 2)))

lemma densityCutoff_decay {p : ℝ} (hp : 0 < p) (hs : p ≤ 1/256) :
    Real.exp (-(densityCutoff p:ℝ)/64) ≤ Real.exp (1/64) * p^(1/512:ℝ) := by
  have hh := (densityCutoff_bounds hp hs).2.2
  have hb : Real.log 2 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith
  have hH : 0 ≤ (densityCutoff p:ℝ)+1 := by positivity
  have hu := mul_le_mul_of_nonneg_left hb hH
  rw [Real.rpow_def_of_pos hp,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

lemma densityCutoff_power {p q : ℝ} (hp : 0 < p) (hs : p ≤ 1/256)
    (hq : 0 < q) (hlog : Real.log q ≤ Real.log 2/4) (n : ℕ) (hn : n ≤ 4)
    (hq1 : 1 ≤ q) :
    p*(2:ℝ)^(densityCutoff p)*q^(n*densityCutoff p) ≤ p^(1/2:ℝ) := by
  have hcut := (densityCutoff_bounds hp hs).2.1
  have hH : 0 ≤ (densityCutoff p:ℝ) := Nat.cast_nonneg _
  have hn' : (n:ℝ) ≤ 4 := by exact_mod_cast hn
  have hln := Real.log_nonneg hq1
  have hl := mul_le_mul_of_nonneg_right hn' hln
  have hnl : (n:ℝ)*Real.log q ≤ Real.log 2 := by linarith
  have hm := mul_le_mul_of_nonneg_left hnl hH
  have heq : p*(2:ℝ)^(densityCutoff p)*q^(n*densityCutoff p) =
      Real.exp (Real.log p+(densityCutoff p:ℝ)*Real.log 2+
        (n*densityCutoff p:ℕ)*Real.log q) := by
    rw [Real.exp_add,Real.exp_add,Real.exp_nat_mul,Real.exp_nat_mul,
      Real.exp_log hp,Real.exp_log hq,Real.exp_log (by norm_num : (0:ℝ)<2)]
  rw [heq,Real.rpow_def_of_pos hp]
  apply Real.exp_le_exp.mpr
  push_cast
  nlinarith

lemma densityCutoff_sparse {p q : ℝ} (hp : 0 < p) (hs : p ≤ 1/256)
    (hq : 0 < q) (hlog : Real.log q ≤ Real.log 2/4) (hq1 : 1 ≤ q) :
    (2:ℝ)^(densityCutoff p)*(p*(q^2)^(densityCutoff p)) ≤ 1/2 := by
  have hh := densityCutoff_power hp hs hq hlog 2 (by decide) hq1
  rw [←pow_mul] at ⊢
  have hle : p^(1/2:ℝ) ≤ 1/2 := by
    have hlogp := log_small_density hp hs
    have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    rw [Real.rpow_def_of_pos hp]
    calc
      _ ≤ Real.exp (-Real.log 2) := by apply Real.exp_le_exp.mpr; nlinarith
      _ = 1/2 := by rw [Real.exp_neg,Real.exp_log (by norm_num : (0:ℝ)<2)]; norm_num
  nlinarith [hh.trans hle]


lemma momentBase_log_exact : Real.log momentBase = Real.log 2/1000 := by
  rw [momentBase,Real.log_rpow (by norm_num)]
  ring

lemma densityCutoff_le_height (d k : ℕ) (hk : 0 < k) :
    densityCutoff ((k:ℝ)/(2:ℝ)^d) ≤ d := by
  have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hp : 0 < (k:ℝ)/(2:ℝ)^d := by positivity
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogk := Real.log_nonneg hk'
  by_cases hx : 0 ≤ -Real.log ((k:ℝ)/(2:ℝ)^d)/(4*Real.log 2)
  · have hh := (le_div_iff₀ (by positivity : 0 < 4*Real.log 2)).mp (Nat.floor_le hx)
    have hd : (0:ℝ) ≤ d := Nat.cast_nonneg _
    have hH : (0:ℝ) ≤ densityCutoff ((k:ℝ)/(2:ℝ)^d) := Nat.cast_nonneg _
    change (densityCutoff ((k:ℝ)/(2:ℝ)^d):ℝ)*(4*Real.log 2) ≤ -Real.log ((k:ℝ)/(2:ℝ)^d) at hh
    rw [Real.log_div (by positivity) (by positivity),Real.log_pow] at hh
    have hle : (densityCutoff ((k:ℝ)/(2:ℝ)^d):ℝ) ≤ d := by nlinarith
    exact_mod_cast hle
  · have hz := Nat.floor_of_nonpos (le_of_not_ge hx)
    simp only [densityCutoff,hz,Nat.zero_le]

noncomputable def densityTailConstant : ℝ :=
  68*Real.exp (1/64)/(1-Real.exp (-(1:ℝ)/64))

lemma densityTailConstant_nonneg : 0 ≤ densityTailConstant := by
  have h := Real.exp_lt_one_iff.mpr (by norm_num : -(1:ℝ)/64 < 0)
  apply div_nonneg (by positivity) (by linarith)

lemma heightDecay_cutoff {p : ℝ} (hp : 0 < p) (hs : p ≤ 1/256) :
    heightDecay (densityCutoff p) ≤ densityTailConstant*p^(1/512:ℝ) := by
  have hden : 0 ≤ 1-Real.exp (-(1:ℝ)/64) := by
    have h := Real.exp_lt_one_iff.mpr (by norm_num : -(1:ℝ)/64 < 0)
    linarith
  have hh := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (densityCutoff_decay hp hs) (by norm_num : (0:ℝ)≤68)) hden
  simpa only [heightDecay,densityTailConstant,mul_assoc,div_mul_eq_mul_div] using hh

lemma sparse_low_algebra (r H k : ℕ) (q : ℝ) :
    (2:ℝ)^r*(2*((2:ℝ)^H*(((k:ℝ)/(2:ℝ)^(H+r))*(q^2)^H))^2) =
    2*k*(((k:ℝ)/(2:ℝ)^(H+r))*(2:ℝ)^H*q^(4*H)) := by
  rw [pow_add,←pow_mul,show 4*H = (2*H)*2 by omega,pow_mul]
  have hH : (2:ℝ)^H ≠ 0 := by positivity
  have hr : (2:ℝ)^r ≠ 0 := by positivity
  field_simp
  ring

lemma palindrome_row_moment_small (d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (hk : 0 < Fintype.card ι)
    (hs : (Fintype.card ι:ℝ)/(2:ℝ)^d ≤ 1/256) :
    palindromeRowMoment d e (1/1000) ≤
      Real.exp (Fintype.card ι*(1+densityTailConstant)*
        ((Fintype.card ι:ℝ)/(2:ℝ)^d)^(1/512:ℝ)) := by
  generalize hpdef : ((Fintype.card ι:ℝ)/(2:ℝ)^d) = p at hs ⊢
  have hp : 0 < p := by rw [←hpdef]; positivity
  have hle := densityCutoff_le_height d (Fintype.card ι) hk
  rw [hpdef] at hle
  obtain ⟨r,hr⟩ := Nat.exists_eq_add_of_le hle
  subst d
  have hH := (densityCutoff_bounds hp hs).1
  have hq := momentBase_one_le
  have hqp : 0 < momentBase := by linarith
  have hlog : Real.log momentBase ≤ Real.log 2/4 := by
    rw [momentBase_log_exact]
    have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    linarith
  have hsp := densityCutoff_sparse hp hs hqp hlog hq
  rw [←hpdef] at hsp
  have hh := palindrome_cost_mgf_cutoff r (densityCutoff p) hH e momentBase hq momentBase_log
    (by simpa only [hpdef] using hsp)
  apply (palindromeRowMoment_le_cost _ e).trans (hh.trans (Real.exp_le_exp.mpr _))
  rw [sparse_low_algebra,hpdef]
  have hlow := densityCutoff_power hp hs hqp hlog 4 (by decide) hq
  have hp1 : p ≤ 1 := by linarith
  have he := Real.rpow_le_rpow_of_exponent_ge hp hp1 (by norm_num : (1:ℝ)/512 ≤ 1/2)
  have hlow' := mul_le_mul_of_nonneg_left (hlow.trans he)
    (by positivity : (0:ℝ)≤2*Fintype.card ι)
  have hhigh := mul_le_mul_of_nonneg_left (heightDecay_cutoff hp hs)
    (Nat.cast_nonneg (Fintype.card ι): (0:ℝ)≤_)
  have hnon : 0 ≤ Fintype.card ι*densityTailConstant*p^(1/512:ℝ) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) densityTailConstant_nonneg)
      (Real.rpow_nonneg (le_of_lt hp) _)
  nlinarith

noncomputable def densityConstant : ℝ :=
  256*(1+heightDecay 1)+1+densityTailConstant

lemma densityConstant_pos : 0 < densityConstant := by
  dsimp [densityConstant]
  have hh := heightDecay_nonneg 1
  have ht := densityTailConstant_nonneg
  linarith

theorem palindrome_row_moment_bound (d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (hk : 0 < Fintype.card ι) :
    palindromeRowMoment d e (1/1000) ≤ Real.exp (densityConstant*Fintype.card ι*
        ((Fintype.card ι:ℝ)/(2:ℝ)^d)^(1/512:ℝ)) := by
  have hp : 0 < (Fintype.card ι:ℝ)/(2:ℝ)^d := by positivity
  have hp1 : (Fintype.card ι:ℝ)/(2:ℝ)^d ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    have h := Fintype.card_le_of_injective e e.injective
    rw [card_positions] at h
    exact_mod_cast h
  have hk0 : (0:ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have hpow := Real.rpow_nonneg (le_of_lt hp) (1/512:ℝ)
  by_cases hs : (Fintype.card ι:ℝ)/(2:ℝ)^d ≤ 1/256
  · apply (palindrome_row_moment_small d e hk hs).trans (Real.exp_le_exp.mpr _)
    have hD : 1+densityTailConstant ≤ densityConstant := by
      dsimp [densityConstant]
      have := heightDecay_nonneg 1
      linarith
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hD hk0) hpow
    nlinarith
  · have hlow : (1:ℝ)/256 ≤ ((Fintype.card ι:ℝ)/(2:ℝ)^d)^(1/512:ℝ) := by
      have he := Real.rpow_le_rpow_of_exponent_ge hp hp1 (by norm_num : (1:ℝ)/512 ≤ 1)
      rw [Real.rpow_one] at he
      exact (le_of_not_ge hs).trans he
    have hD : 256*(1+heightDecay 1) ≤ densityConstant := by
      dsimp [densityConstant]
      have := densityTailConstant_nonneg
      linarith
    apply (palindrome_row_moment_coarse d e).trans (Real.exp_le_exp.mpr _)
    have hD0 : 0 ≤ 1+heightDecay 1 := by have := heightDecay_nonneg 1; linarith
    have ha := mul_le_mul_of_nonneg_left hlow (mul_nonneg (by norm_num : (0:ℝ)≤256) hD0)
    have hb := mul_le_mul_of_nonneg_right hD hpow
    have hc := mul_le_mul_of_nonneg_right (ha.trans hb) hk0
    nlinarith

lemma palindromeRowMoment_nonneg (d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (a : ℝ) : 0 ≤ palindromeRowMoment d e a := by
  apply finiteMean_nonneg
  intro f
  exact Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg _)
    (PairRouting.tupleProbability_nonneg _ _ _)) _

theorem palindrome_log_row_moment (d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (hk : 0 < Fintype.card ι) :
    Real.log (palindromeRowMoment d e (1/1000)) ≤ densityConstant*Fintype.card ι*
        ((Fintype.card ι:ℝ)/(2:ℝ)^d)^(1/512:ℝ) := by
  by_cases hz : palindromeRowMoment d e (1/1000) = 0
  · rw [hz,Real.log_zero]
    exact mul_nonneg (mul_nonneg (le_of_lt densityConstant_pos) (Nat.cast_nonneg _))
      (Real.rpow_nonneg (by positivity) _)
  · exact (Real.log_le_iff_le_exp (lt_of_le_of_ne (palindromeRowMoment_nonneg _ _ _) (Ne.symm hz))).mpr
      (palindrome_row_moment_bound d e hk)

end Thorp


namespace Thorp.StrongSmoothing
open scoped BigOperators

variable {X : Type*} [Fintype X] [Nonempty X]

omit [Nonempty X] in
lemma mean_nonneg (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) : 0 ≤ finiteMean f :=
  finiteMean_nonneg hf

lemma mean_rpow_concave (f : X → ℝ) (hf : ∀ x, 0 ≤ f x)
    {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    finiteMean (fun x => (f x)^a) ≤ (finiteMean f)^a := by
  have hN : (0:ℝ) < Fintype.card X := Nat.cast_pos.mpr Fintype.card_pos
  have hh := (Real.concaveOn_rpow ha ha1).le_map_sum
    (t := Finset.univ) (w := fun _ : X => 1/(Fintype.card X:ℝ))
    (p := f) (fun _ _ => by positivity)
    (by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; field_simp)
    (fun x _ => hf x)
  simpa only [smul_eq_mul,one_div,←Finset.mul_sum,mul_comm _ (∑ _ : X,_),
    ←div_eq_mul_inv,finiteMean] using hh

noncomputable def act (K : Matrix X X ℝ) (f : X → ℝ) (y : X) : ℝ := ∑ x, K x y*f x

omit [Nonempty X] in
lemma act_nonneg (K : Matrix X X ℝ) (hK : ∀ x y, 0 ≤ K x y)
    (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) (y : X) : 0 ≤ act K f y :=
  Finset.sum_nonneg (fun x _ => mul_nonneg (hK x y) (hf x))

omit [Nonempty X] in
lemma act_rpow_le (K : Matrix X X ℝ) (hK : ∀ x y, 0 ≤ K x y)
    (hcol : ∀ y, ∑ x, K x y = 1) (f : X → ℝ) (hf : ∀ x, 0 ≤ f x)
    {b : ℝ} (hb : 1 ≤ b) (y : X) :
    (act K f y)^b ≤ act K (fun x => (f x)^b) y := by
  simpa only [smul_eq_mul,act] using
    (convexOn_rpow hb).map_sum_le (t := Finset.univ) (w := fun x => K x y)
      (p := f) (fun x _ => hK x y) (hcol y) (fun x _ => hf x)

lemma act_one_to_p (K : Matrix X X ℝ) (hK : ∀ x y, 0 ≤ K x y)
    {p A : ℝ} (hp : 1 ≤ p)
    (hm : ∀ x, finiteMean (fun y => ((Fintype.card X:ℝ)*K x y)^p) ≤ Real.exp A)
    (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) :
    finiteMean (fun y => (act K f y)^p) ≤ Real.exp A*(finiteMean f)^p := by
  classical
  let s : ℝ := ∑ x, f x
  have hs : 0 ≤ s := Finset.sum_nonneg (fun x _ => hf x)
  have hN : (0:ℝ) < Fintype.card X := Nat.cast_pos.mpr Fintype.card_pos
  by_cases hz : s=0
  · have hfz : ∀ x, f x=0 := by
      intro x
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => hf x)).mp hz x (Finset.mem_univ _)
    simp only [act,hfz,mul_zero,Finset.sum_const_zero,finiteMean,zero_div,
      Real.zero_rpow (show p ≠ 0 by linarith),mul_zero,le_refl]
  · have hsp : 0 < s := lt_of_le_of_ne hs (Ne.symm hz)
    let w : X → ℝ := fun x => f x/s
    have hw : ∀ x, 0 ≤ w x := fun x => div_nonneg (hf x) hs
    have hws : ∑ x, w x = 1 := by simp only [w,←Finset.sum_div]; exact div_self hz
    have hact (y : X) : act K f y = finiteMean f * ∑ x, w x*((Fintype.card X:ℝ)*K x y) := by
      simp only [act,w,finiteMean,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      have hz' : (∑ x, f x) ≠ 0 := hz
      dsimp [s]
      field_simp [hz',ne_of_gt hN]
    have hj (y : X) : (act K f y)^p ≤ (finiteMean f)^p*
        ∑ x, w x*((Fintype.card X:ℝ)*K x y)^p := by
      rw [hact,Real.mul_rpow (mean_nonneg f hf)
        (Finset.sum_nonneg (fun x _ => mul_nonneg (hw x) (mul_nonneg hN.le (hK x y))))]
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (mean_nonneg f hf) _)
      exact (convexOn_rpow hp).map_sum_le
        (fun x _ => hw x) hws (fun x _ => mul_nonneg hN.le (hK x y))
    have hh := finiteMean_mono hj
    have he : finiteMean (fun y => (finiteMean f)^p*
        ∑ x, w x*((Fintype.card X:ℝ)*K x y)^p) =
        (finiteMean f)^p * ∑ x, w x*finiteMean (fun y => ((Fintype.card X:ℝ)*K x y)^p) := by
      simp_rw [mul_comm ((finiteMean f)^p), finiteMean_mul_const,
        finiteMean_sum, mul_comm (w _), finiteMean_mul_const]
    rw [he] at hh
    apply hh.trans
    have hsum : (∑ x, w x*finiteMean (fun y => ((Fintype.card X:ℝ)*K x y)^p)) ≤ Real.exp A := by
      calc
        _ ≤ ∑ x, w x*Real.exp A := Finset.sum_le_sum
          (fun x _ => mul_le_mul_of_nonneg_left (hm x) (hw x))
        _ = Real.exp A := by rw [←Finset.sum_mul,hws,one_mul]
    simpa only [mul_comm (Real.exp A)] using
      mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg (mean_nonneg f hf) _)

lemma act_b_to_pb (K : Matrix X X ℝ) (hK : ∀ x y, 0 ≤ K x y)
    (hcol : ∀ y, ∑ x, K x y = 1) {p A b : ℝ} (hp : 1 ≤ p) (hb : 1 ≤ b)
    (hm : ∀ x, finiteMean (fun y => ((Fintype.card X:ℝ)*K x y)^p) ≤ Real.exp A)
    (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) :
    finiteMean (fun y => (act K f y)^(b*p)) ≤
      Real.exp A*(finiteMean (fun x => (f x)^b))^p := by
  calc
    _ ≤ finiteMean (fun y => (act K (fun x => (f x)^b) y)^p) := by
      apply finiteMean_mono
      intro y
      rw [Real.rpow_mul (act_nonneg K hK f hf y)]
      exact Real.rpow_le_rpow (Real.rpow_nonneg (act_nonneg K hK f hf y) _) (act_rpow_le K hK hcol f hf hb y) (by linarith)
    _ ≤ _ := act_one_to_p K hK hp hm _ (fun x => Real.rpow_nonneg (hf x) _)

variable [DecidableEq X]

omit [Nonempty X] in
lemma kernel_pow_nonneg (K : Matrix X X ℝ) (hK : ∀ x y, 0 ≤ K x y) (r : ℕ) :
    ∀ x y, 0 ≤ (K^r) x y := by
  classical
  induction r with
  | zero => intro x y; simp only [pow_zero,Matrix.one_apply]; split_ifs <;> norm_num
  | succ r ih =>
    intro x y
    rw [pow_succ,Matrix.mul_apply]
    exact Finset.sum_nonneg (fun z _ => mul_nonneg (ih x z) (hK z y))

omit [Nonempty X] in
lemma kernel_pow_row (K : Matrix X X ℝ) (hrow : ∀ x, ∑ y, K x y = 1) (r : ℕ) :
    ∀ x, ∑ y, (K^r) x y = 1 := by
  classical
  induction r with
  | zero => intro x; simp [Matrix.one_apply]
  | succ r ih =>
    intro x
    simp only [pow_succ,Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp only [←Finset.mul_sum,hrow,mul_one,ih]

noncomputable def rowDensity (K : Matrix X X ℝ) (r : ℕ) (x y : X) : ℝ :=
  (Fintype.card X:ℝ)*(K^r) x y

omit [Nonempty X] in
lemma rowDensity_nonneg (K : Matrix X X ℝ) (hK : ∀ x y, 0 ≤ K x y) (r : ℕ) (x y : X) :
    0 ≤ rowDensity K r x y := mul_nonneg (Nat.cast_nonneg _) (kernel_pow_nonneg K hK r x y)

omit [Nonempty X] in
lemma rowDensity_succ (K : Matrix X X ℝ) (r : ℕ) (x y : X) :
    rowDensity K (r+1) x y = act K (rowDensity K r x) y := by
  simp only [rowDensity,pow_succ,Matrix.mul_apply,act,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  ring

lemma rowDensity_mean (K : Matrix X X ℝ) (hrow : ∀ x, ∑ y, K x y = 1) (r : ℕ) (x : X) :
    finiteMean (rowDensity K r x) = 1 := by
  have hN : (Fintype.card X:ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr Fintype.card_pos)
  simp only [finiteMean,rowDensity,←Finset.mul_sum,kernel_pow_row K hrow,mul_one,div_self hN]

lemma rowDensity_moment_iter (K : Matrix X X ℝ) (hK : ∀ x y, 0 ≤ K x y)
    (hrow : ∀ x, ∑ y, K x y = 1) (hcol : ∀ y, ∑ x, K x y = 1)
    {p A : ℝ} (hp : 1 ≤ p) (hA : 0 ≤ A)
    (hm : ∀ x, finiteMean (fun y => ((Fintype.card X:ℝ)*K x y)^p) ≤ Real.exp A)
    (r : ℕ) (x : X) :
    finiteMean (fun y => (rowDensity K r x y)^(p^r)) ≤ Real.exp (A*r*p^r) := by
  induction r with
  | zero => simp [rowDensity_mean K hrow]
  | succ r ih =>
    have hpr : 1 ≤ p^r := one_le_pow₀ hp
    have hps : 1 ≤ p^(r+1) := one_le_pow₀ hp
    simp_rw [rowDensity_succ]
    calc
      _ ≤ Real.exp A*(finiteMean (fun y => (rowDensity K r x y)^(p^r)))^p := by
        rw [pow_succ]
        exact act_b_to_pb K hK hcol hp hpr hm _ (rowDensity_nonneg K hK r x)
      _ ≤ Real.exp A*(Real.exp (A*r*p^r))^p := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        exact Real.rpow_le_rpow (mean_nonneg _ (fun y => Real.rpow_nonneg
          (rowDensity_nonneg K hK r x y) _)) ih (le_trans zero_le_one hp)
      _ = Real.exp (A+A*r*p^(r+1)) := by rw [←Real.exp_mul,←Real.exp_add,pow_succ]; congr 1; ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have hh := mul_le_mul_of_nonneg_left hps hA
        push_cast
        nlinarith

lemma rowDensity_second_moment (K : Matrix X X ℝ) (hK : ∀ x y, 0 ≤ K x y)
    (hrow : ∀ x, ∑ y, K x y = 1) (hcol : ∀ y, ∑ x, K x y = 1)
    {p A : ℝ} (hp : 1 ≤ p) (hA : 0 ≤ A)
    (hm : ∀ x, finiteMean (fun y => ((Fintype.card X:ℝ)*K x y)^p) ≤ Real.exp A)
    (r : ℕ) (hr : 2 ≤ p^r) (x : X) :
    finiteMean (fun y => (rowDensity K r x y)^2) ≤ Real.exp (2*A*r) := by
  have hpos : 0 < p^r := by linarith
  have hj := mean_rpow_concave (fun y => (rowDensity K r x y)^(p^r))
    (fun y => Real.rpow_nonneg (rowDensity_nonneg K hK r x y) _)
    (a := 2/(p^r)) (by positivity) ((div_le_one hpos).mpr hr)
  have he (y : X) : ((rowDensity K r x y)^(p^r))^(2/(p^r)) = (rowDensity K r x y)^2 := by
    rw [←Real.rpow_mul (rowDensity_nonneg K hK r x y)]
    rw [mul_div_cancel₀ _ (ne_of_gt hpos),Real.rpow_two]
  simp_rw [he] at hj
  apply hj.trans
  calc
    _ ≤ (Real.exp (A*r*p^r))^(2/(p^r)) :=
      Real.rpow_le_rpow (mean_nonneg _ (fun y => Real.rpow_nonneg
        (rowDensity_nonneg K hK r x y) _)) (rowDensity_moment_iter K hK hrow hcol hp hA hm r x)
        (by positivity)
    _ = _ := by rw [←Real.exp_mul]; congr 1; field_simp [ne_of_gt hpos]

lemma symmetric_kernel_smoothing (K : Matrix X X ℝ) (hK : ∀ x y, 0 ≤ K x y)
    (hrow : ∀ x, ∑ y, K x y = 1) (hcol : ∀ y, ∑ x, K x y = 1)
    (hsym : K.IsSymm) {p A : ℝ} (hp : 1 ≤ p) (hA : 0 ≤ A)
    (hm : ∀ x, finiteMean (fun y => ((Fintype.card X:ℝ)*K x y)^p) ≤ Real.exp A)
    (r : ℕ) (hr : 2 ≤ p^r) (x y : X) :
    (K^(2*r)) x y ≤ Real.exp (2*A*r)/(Fintype.card X:ℝ) := by
  have hN : (0:ℝ) < Fintype.card X := Nat.cast_pos.mpr Fintype.card_pos
  have hs : ∀ z, (K^r) z y = (K^r) y z := fun z => (hsym.pow r).apply y z
  have he : (Fintype.card X:ℝ)*(K^(2*r)) x y =
      finiteMean (fun z => rowDensity K r x z*rowDensity K r y z) := by
    simp only [finiteMean,rowDensity,two_mul,pow_add,Matrix.mul_apply,hs,Finset.mul_sum]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro z _
    field_simp
  have hh : finiteMean (fun z => rowDensity K r x z*rowDensity K r y z) ≤
      Real.exp (2*A*r) := by
    calc
      _ ≤ finiteMean (fun z => ((rowDensity K r x z)^2+(rowDensity K r y z)^2)/2) := by
        apply finiteMean_mono
        intro z
        nlinarith [sq_nonneg (rowDensity K r x z-rowDensity K r y z)]
      _ = (finiteMean (fun z => (rowDensity K r x z)^2)+
          finiteMean (fun z => (rowDensity K r y z)^2))/2 := by
        simp only [div_eq_mul_inv,finiteMean_mul_const,finiteMean_add]
      _ ≤ _ := by
        have hx := rowDensity_second_moment K hK hrow hcol hp hA hm r hr x
        have hy := rowDensity_second_moment K hK hrow hcol hp hA hm r hr y
        linarith
  apply (le_div_iff₀ hN).mpr
  simpa only [←he,mul_comm (Fintype.card X:ℝ)] using hh

lemma density_exponent_numeric : 2 ≤ (1+(1/1000:ℝ))^(1000:ℕ) := by
  calc
    (2:ℝ) = 1+(1000:ℝ)*(1/1000) := by norm_num
    _ ≤ _ := by simpa only [Nat.cast_ofNat] using
      (one_add_mul_le_pow (a := (1/1000:ℝ)) (by norm_num) 1000)

end Thorp.StrongSmoothing

namespace Thorp.StrongSmoothing.PermLaw
open scoped BigOperators
variable {X Ω Ω' : Type*} [Fintype X] [DecidableEq X] [Fintype Ω] [Fintype Ω']

noncomputable def kernel (P : Ω → Equiv.Perm X) : Matrix X X ℝ :=
  fun x y => finiteMean (fun ω => if P ω x = y then (1:ℝ) else 0)

omit [Fintype X] in
lemma nonneg (P : Ω → Equiv.Perm X) (x y : X) : 0 ≤ kernel P x y := by
  exact finiteMean_nonneg (fun ω => by split_ifs <;> norm_num)

lemma row [Nonempty Ω] (P : Ω → Equiv.Perm X) (x : X) : ∑ y, kernel P x y = 1 := by
  simp only [kernel,←finiteMean_sum]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,↓reduceIte,finiteMean_const]

omit [Fintype X] in
lemma inverse (P : Ω → Equiv.Perm X) : kernel (fun ω => (P ω)⁻¹) = (kernel P).transpose := by
  ext x y
  apply finiteMean_congr
  intro ω
  have he : (P ω)⁻¹ x=y ↔ P ω y=x := by
    change (P ω).symm x=y ↔ P ω y=x
    exact (Equiv.symm_apply_eq (P ω)).trans eq_comm
  simp only [he]

lemma col [Nonempty Ω] (P : Ω → Equiv.Perm X) (y : X) : ∑ x, kernel P x y = 1 := by
  have hh := row (fun ω => (P ω)⁻¹) y
  rw [inverse] at hh
  exact hh

lemma mul (P : Ω → Equiv.Perm X) (Q : Ω' → Equiv.Perm X) :
    kernel (fun ω : Ω × Ω' => P ω.1*Q ω.2) = kernel Q*kernel P := by
  ext x y
  simp only [Matrix.mul_apply,kernel]
  have he (ω : Ω × Ω') :
      (if (P ω.1*Q ω.2) x=y then (1:ℝ) else 0) =
        ∑ z : X, (if P ω.1 z=y then (1:ℝ) else 0)*(if Q ω.2 x=z then (1:ℝ) else 0) := by
    simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,↓reduceIte]
    rfl
  change finiteMean (fun ω : Ω × Ω' => if (P ω.1*Q ω.2) x=y then (1:ℝ) else 0) = _
  simp_rw [he]
  rw [finiteMean_sum]
  apply Finset.sum_congr rfl
  intro z _
  exact (finiteMean_prod_mul (fun ω : Ω => if P ω z=y then (1:ℝ) else 0)
    (fun ω : Ω' => if Q ω x=z then (1:ℝ) else 0)).trans (mul_comm _ _)

omit [Fintype X] in
lemma conjugate (P : Ω → Equiv.Perm X) (e : Equiv.Perm X) (x y : X) :
    kernel (fun ω => e*P ω*e⁻¹) x y = kernel P (e.symm x) (e.symm y) := by
  apply finiteMean_congr
  intro ω
  have he : (e*P ω*e⁻¹) x=y ↔ P ω (e.symm x)=e.symm y := by
    change e (P ω (e.symm x))=y ↔ _
    exact (Equiv.eq_symm_apply e).symm
  simp only [he]

end Thorp.StrongSmoothing.PermLaw

namespace Thorp.StrongSmoothing
open scoped BigOperators

section MatrixHelpers
variable {X : Type*} [Fintype X] [DecidableEq X]

omit [DecidableEq X] in
lemma mul_nonneg_entries (A B : Matrix X X ℝ) (hA : ∀ x y, 0 ≤ A x y)
    (hB : ∀ x y, 0 ≤ B x y) (x y : X) : 0 ≤ (A*B) x y :=
  Finset.sum_nonneg (fun z _ => mul_nonneg (hA x z) (hB z y))

omit [DecidableEq X] in
lemma mul_row (A B : Matrix X X ℝ) (hA : ∀ x, ∑ y, A x y = 1)
    (hB : ∀ x, ∑ y, B x y = 1) (x : X) : ∑ y, (A*B) x y = 1 := by
  simp only [Matrix.mul_apply]
  rw [Finset.sum_comm]
  simp only [←Finset.mul_sum,hB,mul_one,hA]

omit [DecidableEq X] in
lemma mul_col (A B : Matrix X X ℝ) (hA : ∀ y, ∑ x, A x y = 1)
    (hB : ∀ y, ∑ x, B x y = 1) (y : X) : ∑ x, (A*B) x y = 1 := by
  simp only [Matrix.mul_apply]
  rw [Finset.sum_comm]
  simp only [←Finset.sum_mul,hA,one_mul,hB]

omit [DecidableEq X] in
lemma bound_mul_left (A B : Matrix X X ℝ) (hA : ∀ x y, 0 ≤ A x y)
    (hrow : ∀ x, ∑ y, A x y = 1) {D : ℝ} (hB : ∀ x y, B x y ≤ D) :
    ∀ x y, (A*B) x y ≤ D := by
  intro x y
  calc
    _ ≤ ∑ z, A x z*D := Finset.sum_le_sum (fun z _ => mul_le_mul_of_nonneg_left (hB z y) (hA x z))
    _ = D := by rw [←Finset.sum_mul,hrow,one_mul]

omit [DecidableEq X] in
lemma bound_mul_right (A B : Matrix X X ℝ) (hB : ∀ x y, 0 ≤ B x y)
    (hcol : ∀ y, ∑ x, B x y = 1) {D : ℝ} (hA : ∀ x y, A x y ≤ D) :
    ∀ x y, (A*B) x y ≤ D := by
  intro x y
  calc
    _ ≤ ∑ z, D*B z y := Finset.sum_le_sum (fun z _ => mul_le_mul_of_nonneg_right (hA x z) (hB z y))
    _ = D := by rw [←Finset.mul_sum,hcol,mul_one]

lemma sandwich_power (A B : Matrix X X ℝ) (r : ℕ) : A*(B*A)^r*B = (A*B)^(r+1) := by
  induction r with
  | zero => simp
  | succ r ih =>
    calc
      _ = (A*(B*A)^r*B)*(A*B) := by rw [pow_succ]; noncomm_ring
      _ = (A*B)^(r+1)*(A*B) := by rw [ih]
      _ = _ := (pow_succ (A*B) (r+1)).symm

end MatrixHelpers

section TupleAction
variable {ι β Ω : Type*} [Fintype ι] [Fintype β] [DecidableEq β] [Fintype Ω]

def tuplePerm (P : Equiv.Perm β) : Equiv.Perm (ι ↪ β) where
  toFun x := x.trans P.toEmbedding
  invFun x := x.trans P.symm.toEmbedding
  left_inv x := by ext i; simp
  right_inv x := by ext i; simp

omit [Fintype ι] [Fintype β] [DecidableEq β] in
@[simp] lemma tuplePerm_apply (P : Equiv.Perm β) (x : ι ↪ β) (i : ι) :
    tuplePerm P x i = P (x i) := rfl

omit [Fintype ι] [Fintype β] [DecidableEq β] in
lemma tuplePerm_mul (P Q : Equiv.Perm β) :
    tuplePerm (ι := ι) (P*Q) = tuplePerm P*tuplePerm Q := by
  ext x i
  rfl

omit [Fintype ι] [Fintype β] [DecidableEq β] in
lemma tuplePerm_inverse (P : Equiv.Perm β) :
    tuplePerm (ι := ι) P⁻¹ = (tuplePerm P)⁻¹ := by
  ext x i
  rfl

omit [Fintype β] in
lemma tupleProbability_kernel (P : Ω → Equiv.Perm β) (x y : ι ↪ β) :
    PairRouting.tupleProbability P x y = PermLaw.kernel (fun ω => tuplePerm (P ω)) x y := by
  classical
  apply finiteMean_congr
  intro ω
  have he : (∀ i, P ω (x i) = y i) ↔ tuplePerm (P ω) x = y := by
    constructor
    · intro h; ext i; exact h i
    · intro h i; exact congrArg (fun z : ι ↪ β => z i) h
  simp only [he]
end TupleAction

lemma sweepKernel_law (d l : ℕ) (order : Equiv.Perm (Fin d)) :
    sweepKernel d l order = PermLaw.kernel (fun ω => tuplePerm (ι := Fin l) (sweep d order ω)) := by
  ext x y
  exact tupleProbability_kernel _ x y

lemma reflectedKernel_conjugate (d l : ℕ) (order : Equiv.Perm (Fin d)) (x y : Tuples d l) :
    reflectedKernel d l order false x y =
      PairRouting.tupleProbability (palindromePerm d)
        ((tuplePerm (coordinateRelabel d order)).symm x)
        ((tuplePerm (coordinateRelabel d order)).symm y) := by
  classical
  let e : Equiv.Perm (Tuples d l) := tuplePerm (coordinateRelabel d order)
  let P := fun ω => tuplePerm (ι := Fin l) (butterflyPerm d (decodeButterfly d ω))
  have hA : sweepKernel d l order = PermLaw.kernel (fun ω => e*P ω*e⁻¹) := by
    rw [sweepKernel_law]
    simp only [sweep,tuplePerm_mul,tuplePerm_inverse]
    rfl
  rw [reflectedKernel,ite_eq_right Bool.false_ne_true,hA]
  rw [←PermLaw.inverse,←PermLaw.mul]
  have hprod : (fun ω : BenesCoins d => (e*P ω.1*e⁻¹)*((e*P ω.2*e⁻¹)⁻¹)) =
      fun ω : BenesCoins d => e*tuplePerm (ι := Fin l) (palindromePerm d ω)*e⁻¹ := by
    funext ω
    simp only [mul_inv_rev,inv_inv,palindromePerm,tuplePerm_mul]
    change (e*P ω.1*e⁻¹)*(e*(P ω.2)⁻¹*e⁻¹) = e*(P ω.1*(P ω.2)⁻¹)*e⁻¹
    group
  rw [hprod,PermLaw.conjugate,tupleProbability_kernel]


lemma sweepKernel_nonneg (d l : ℕ) (order : Equiv.Perm (Fin d)) (x y : Tuples d l) :
    0 ≤ sweepKernel d l order x y := PairRouting.tupleProbability_nonneg _ _ _

lemma sweepKernel_row (d l : ℕ) (order : Equiv.Perm (Fin d)) (x : Tuples d l) :
    ∑ y, sweepKernel d l order x y = 1 := by
  rw [sweepKernel_law]
  exact PermLaw.row _ _

lemma sweepKernel_col (d l : ℕ) (order : Equiv.Perm (Fin d)) (y : Tuples d l) :
    ∑ x, sweepKernel d l order x y = 1 := by
  rw [sweepKernel_law]
  exact PermLaw.col _ _

lemma reflected_nonneg (d l : ℕ) (order : Equiv.Perm (Fin d)) (x y : Tuples d l) :
    0 ≤ reflectedKernel d l order false x y := by
  exact mul_nonneg_entries _ _ (fun x y => sweepKernel_nonneg d l order y x)
    (sweepKernel_nonneg d l order) x y

lemma reflected_row (d l : ℕ) (order : Equiv.Perm (Fin d)) (x : Tuples d l) :
    ∑ y, reflectedKernel d l order false x y = 1 :=
  mul_row _ _ (sweepKernel_col d l order) (sweepKernel_row d l order) x

lemma reflected_col (d l : ℕ) (order : Equiv.Perm (Fin d)) (y : Tuples d l) :
    ∑ x, reflectedKernel d l order false x y = 1 :=
  mul_col _ _ (sweepKernel_row d l order) (sweepKernel_col d l order) y

lemma reflected_symmetric (d l : ℕ) (order : Equiv.Perm (Fin d)) :
    (reflectedKernel d l order false).IsSymm := Matrix.isSymm_transpose_mul_self _

lemma reflected_moment (d l : ℕ) (order : Equiv.Perm (Fin d)) (x : Tuples d l) :
    finiteMean (fun y : Tuples d l =>
      ((Fintype.card (Tuples d l):ℝ)*reflectedKernel d l order false x y)^(1+(1/1000:ℝ))) ≤
      Real.exp (l*(1+heightDecay 1)) := by
  classical
  let e : Equiv.Perm (Tuples d l) := tuplePerm (coordinateRelabel d order)
  simp_rw [reflectedKernel_conjugate]
  have he := finiteMean_equiv e (fun y : Tuples d l =>
    ((Fintype.card (Tuples d l):ℝ)*PairRouting.tupleProbability (palindromePerm d) (e.symm x) y)^
      (1+(1/1000:ℝ)))
  change finiteMean (fun y =>
    ((Fintype.card (Tuples d l):ℝ)*PairRouting.tupleProbability (palindromePerm d) (e.symm x) (e.symm y))^
      (1+(1/1000:ℝ))) ≤ _
  rw [←he]
  simpa only [palindromeRowMoment,Fintype.card_fin] using palindrome_row_moment_coarse d (e.symm x)

lemma tuples_card (d l : ℕ) : Fintype.card (Tuples d l) = (2^d).descFactorial l := by
  simp only [Tuples,Fintype.card_embedding_eq,Fintype.card_fin,card_positions]

lemma canonical_pointwise (d l : ℕ) (order : Equiv.Perm (Fin d)) (x y : Tuples d l) :
    ((reflectedKernel d l order false)^2000) x y ≤
      Real.exp ((2000*(1+heightDecay 1))*l)/((2^d).descFactorial l:ℝ) := by
  let : Nonempty (Tuples d l) := ⟨x⟩
  have hh := symmetric_kernel_smoothing (reflectedKernel d l order false)
    (reflected_nonneg d l order) (reflected_row d l order) (reflected_col d l order)
    (reflected_symmetric d l order) (p := 1+(1/1000:ℝ)) (A := l*(1+heightDecay 1))
    (by norm_num) (mul_nonneg (Nat.cast_nonneg _) (by linarith [heightDecay_nonneg 1]))
    (reflected_moment d l order) 1000 density_exponent_numeric x y
  have he : 2*((l:ℝ)*(1+heightDecay 1))*(1000:ℝ) = (2000*(1+heightDecay 1))*l := by ring
  norm_num only [show 2*1000=2000 by norm_num,Nat.cast_ofNat] at hh
  simpa only [he,tuples_card] using hh

lemma both_pointwise (d l : ℕ) (order : Equiv.Perm (Fin d)) (orientation : Bool)
    (x y : Tuples d l) :
    ((reflectedKernel d l order orientation)^2001) x y ≤
      Real.exp ((2000*(1+heightDecay 1))*l)/((2^d).descFactorial l:ℝ) := by
  cases orientation
  · change ((reflectedKernel d l order false)^(2000+1)) x y ≤ _
    rw [pow_succ]
    exact bound_mul_right _ _ (reflected_nonneg d l order) (reflected_col d l order)
      (canonical_pointwise d l order) x y
  · let A := sweepKernel d l order
    change ((A*A.transpose)^(2000+1)) x y ≤ _
    rw [←sandwich_power]
    apply bound_mul_right _ _ (fun x y => sweepKernel_nonneg d l order y x)
      (sweepKernel_row d l order)
    exact bound_mul_left _ _ (sweepKernel_nonneg d l order) (sweepKernel_row d l order)
      (canonical_pointwise d l order)

lemma regular_trace_bound (d : ℕ) (order : Equiv.Perm (Fin d)) :
    regularAbsoluteEvenTrace d order 2001 ≤ Real.exp ((2000*(1+heightDecay 1))*(2:ℝ)^d) := by
  have hn : 0 < Fintype.card (Tuples d (2^d)) := by
    rw [tuples_card,Nat.descFactorial_self]
    exact Nat.factorial_pos _
  have hn' : (Fintype.card (Tuples d (2^d)):ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hn)
  calc
    _ ≤ ∑ x : Tuples d (2^d), Real.exp ((2000*(1+heightDecay 1))*(2^d:ℕ)) /
        ((2^d).descFactorial (2^d):ℝ) := by
      apply Finset.sum_le_sum
      intro x _
      exact both_pointwise d (2^d) order false x x
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,←tuples_card]
      push_cast
      field_simp

theorem strong_smoothing : MainStatement := by
  refine ⟨2001,by norm_num,2000*(1+heightDecay 1),?_,regular_trace_bound⟩
  intro d l _ order orientation x y
  exact both_pointwise d l order orientation x y

end Thorp.StrongSmoothing

end ThorpNine.Smoothing

end OAI
