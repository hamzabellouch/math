import Mathlib
import OAI.Probability.ThorpRouting.SparseSaving.ParallelFreshPre

namespace OAI

namespace ThorpNine.SparseSaving

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

variable {α : Type*} [Fintype α] [DecidableEq α]

lemma orbitSet_eq_of_agree (p q : Equiv.Perm α) (x : α)
    (h : ∀ z ∈ orbitSet p x, p z = q z) : orbitSet p x = orbitSet q x := by
  have hp (n : ℕ) : (p^n) x ∈ orbitSet p x := by
    apply (mem_orbitSet _ _ _).mpr
    exact Equiv.Perm.sameCycle_pow_right.mpr (Equiv.Perm.SameCycle.refl _ _)
  have he (n : ℕ) : (p^n) x = (q^n) x := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ',pow_succ',Equiv.Perm.mul_apply,Equiv.Perm.mul_apply,←ih]
      exact h _ (hp n)
  ext y
  simp only [mem_orbitSet]
  constructor
  · intro hy
    obtain ⟨n,hn⟩ := hy.exists_nat_pow_eq
    rw [←hn,he]
    exact Equiv.Perm.sameCycle_pow_right.mpr (Equiv.Perm.SameCycle.refl _ _)
  · intro hy
    obtain ⟨n,hn⟩ := hy.exists_nat_pow_eq
    rw [←hn,←he]
    exact Equiv.Perm.sameCycle_pow_right.mpr (Equiv.Perm.SameCycle.refl _ _)

noncomputable def survivingCycle (p q : Equiv.Perm α) (S B : Finset α)
    (h : ∀ x ∉ B, p x = q x) (C : RoutingNetwork.SelectedCycle p S)
    (hC : ∀ x ∈ C.val, x ∉ B) : RoutingNetwork.SelectedCycle q S := by
  refine ⟨C.val,?_,C.property.2⟩
  obtain ⟨x,hx⟩ := C.property.1
  refine ⟨x,hx.trans (orbitSet_eq_of_agree p q x ?_)⟩
  intro z hz
  exact h z (hC z (hx ▸ hz))

noncomputable def perturbCycleMap (p q : Equiv.Perm α) (S B : Finset α)
    (h : ∀ x ∉ B, p x = q x) (C : RoutingNetwork.SelectedCycle p S) :
    RoutingNetwork.SelectedCycle q S ⊕ {x // x ∈ B} := by
  classical
  by_cases hb : ∃ x ∈ C.val, x ∈ B
  · exact Sum.inr ⟨hb.choose,hb.choose_spec.2⟩
  · exact Sum.inl (survivingCycle p q S B h C (by simpa only [not_exists,not_and] using hb))

lemma perturbCycleMap_injective (p q : Equiv.Perm α) (S B : Finset α)
    (h : ∀ x ∉ B, p x = q x) : Function.Injective (perturbCycleMap p q S B h) := by
  classical
  intro C D he
  by_cases hC : ∃ x ∈ C.val, x ∈ B <;>
    by_cases hD : ∃ x ∈ D.val, x ∈ B
  · simp only [perturbCycleMap,dite_eq_left hC,dite_eq_left hD,Sum.inr.injEq] at he
    have hx : hC.choose = hD.choose := congrArg Subtype.val he
    exact RoutingNetwork.SelectedCycle.eq_of_mem C D hC.choose_spec.1
      (hx.symm ▸ hD.choose_spec.1)
  · simp only [perturbCycleMap,dite_eq_left hC,dite_eq_right hD] at he
    cases he
  · simp only [perturbCycleMap,dite_eq_right hC,dite_eq_left hD] at he
    cases he
  · simp only [perturbCycleMap,dite_eq_right hC,dite_eq_right hD,Sum.inl.injEq] at he
    have hval : C.val = D.val := congrArg (fun Z : RoutingNetwork.SelectedCycle q S => Z.val) he
    exact Subtype.ext hval

theorem selectedCycle_perturb_le (p q : Equiv.Perm α) (S B : Finset α)
    (h : ∀ x ∉ B, p x = q x) :
    Fintype.card (RoutingNetwork.SelectedCycle p S) ≤
      Fintype.card (RoutingNetwork.SelectedCycle q S)+B.card := by
  have hh := Fintype.card_le_of_injective _ (perturbCycleMap_injective p q S B h)
  simpa only [Fintype.card_sum,Fintype.card_coe] using hh


noncomputable def permDistance (p q : Equiv.Perm α) : ℕ :=
  (Finset.univ.filter (fun x => p x ≠ q x)).card

lemma permDistance_sum (p q : Equiv.Perm α) :
    permDistance p q = ∑ x : α, if p x = q x then 0 else 1 := by
  classical
  simp [permDistance,Finset.card_filter]

lemma permDistance_refl (p : Equiv.Perm α) : permDistance p p = 0 := by
  simp [permDistance]

lemma permDistance_le (p q : Equiv.Perm α) : permDistance p q ≤ Fintype.card α :=
  (Finset.card_filter_le _ _).trans_eq (Finset.card_univ)

lemma permDistance_symm (p q : Equiv.Perm α) : permDistance p q = permDistance q p := by
  simp only [permDistance,ne_comm]

lemma permDistance_triangle (p q r : Equiv.Perm α) :
    permDistance p r ≤ permDistance p q+permDistance q r := by
  classical
  simp only [permDistance_sum,←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  by_cases hpq : p x = q x <;> by_cases hqr : q x = r x <;>
    by_cases hpr : p x = r x <;> simp only [hpq,hqr,hpr,↓reduceIte] <;>
    omega

lemma permDistance_mul_left (p q g : Equiv.Perm α) :
    permDistance (g*p) (g*q) = permDistance p q := by
  classical
  unfold permDistance
  congr 1
  ext x
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  exact not_congr g.injective.eq_iff

lemma permDistance_mul_right (p q g : Equiv.Perm α) :
    permDistance (p*g) (q*g) = permDistance p q := by
  classical
  simp only [permDistance_sum,Equiv.Perm.mul_apply]
  exact Fintype.sum_equiv g _ _ (fun _ => rfl)

lemma permDistance_inv (p q : Equiv.Perm α) : permDistance p⁻¹ q⁻¹ = permDistance p q := by
  have hh := permDistance_mul_left p⁻¹ q⁻¹ q
  have hhh := permDistance_mul_right (q*p⁻¹) 1 p
  simp only [mul_inv_cancel,one_mul,inv_mul_cancel_right] at hh hhh
  rw [←hhh] at hh
  rw [←hh,permDistance_symm]

lemma permDistance_mul_le (p q g h : Equiv.Perm α) :
    permDistance (p*g) (q*h) ≤ permDistance p q+permDistance g h := by
  have hh := permDistance_triangle (p*g) (q*g) (q*h)
  simpa only [permDistance_mul_left,permDistance_mul_right] using hh

lemma selectedCycle_distance_le (p q : Equiv.Perm α) (S : Finset α) :
    Fintype.card (RoutingNetwork.SelectedCycle p S) ≤
      Fintype.card (RoutingNetwork.SelectedCycle q S)+permDistance p q := by
  apply selectedCycle_perturb_le
  intro x hx
  simpa only [Finset.mem_filter,Finset.mem_univ,true_and,not_not] using hx

lemma permDistance_alternating (p q : Equiv.Perm α) :
    permDistance (CycleColoring.alternatingPerm p) (CycleColoring.alternatingPerm q) = permDistance p q := by
  classical
  simp only [permDistance_sum,Fintype.sum_prod_type,Fintype.sum_bool]
  simp [CycleColoring.alternatingPerm]

lemma alternatingCycles_distance_le {ι : Type*} [Fintype ι]
    (e : ι ↪ Bool × α) (p q : Bool → Equiv.Perm α) :
    PairRouting.alternatingCycles e p ≤ PairRouting.alternatingCycles e q+
      (permDistance (p false) (q false)+permDistance (p true) (q true)) := by
  have hh := selectedCycle_distance_le
    (CycleColoring.alternatingPerm (PairRouting.alternatingProjection p))
    (CycleColoring.alternatingPerm (PairRouting.alternatingProjection q)) (PairRouting.labelSet e)
  rw [permDistance_alternating] at hh
  apply hh.trans
  apply Nat.add_le_add_left
  dsimp only [PairRouting.alternatingProjection]
  exact (permDistance_mul_le _ _ _ _).trans_eq (by
    change permDistance (p false)⁻¹ (q false)⁻¹ + _ = _
    rw [permDistance_inv])

end Thorp
namespace Thorp

def centralBlockPerm (L : ℕ) : (r : ℕ) → (Card r → Equiv.Perm (Card L)) →
    Equiv.Perm (Card (L+r))
  | 0, C => C (fun j => Fin.elim0 j)
  | r+1, C => childLift (fun b => centralBlockPerm L r (fun u => C (Fin.cons b u)))

def centralPalindromePerm (L r : ℕ) (C : Card r → Equiv.Perm (Card L))
    (ω : BenesCoins (L+r)) : Equiv.Perm (Card (L+r)) :=
  butterflyPerm (L+r) (decodeButterfly (L+r) ω.1) * centralBlockPerm L r C *
    (butterflyPerm (L+r) (decodeButterfly (L+r) ω.2))⁻¹

lemma centralPalindromePerm_step (L r : ℕ) (C : Card (r+1) → Equiv.Perm (Card L))
    (c : BenesCoins (L+r) × BenesCoins (L+r))
    (coins : (Card (L+r) → Bool) × (Card (L+r) → Bool)) :
    centralPalindromePerm L (r+1) C ((benesStepEquiv (L+r)).symm (c,coins)) =
      pairSwitch coins.2 * childLift (fun b => centralPalindromePerm L r
        (fun u => C (Fin.cons b u)) (if b then c.2 else c.1)) * pairSwitch coins.1 := by
  change ((butterflyPerm (L+r+1) (decodeButterfly (L+r+1)
      ((coinStepEquiv (L+r)).symm ((c.1.1,c.2.1),coins.2))))) *
    childLift (fun b => centralBlockPerm L r (fun u => C (Fin.cons b u))) *
    (butterflyPerm (L+r+1) (decodeButterfly (L+r+1)
      ((coinStepEquiv (L+r)).symm ((c.1.2,c.2.2),coins.1))))⁻¹ = _
  rw [butterflyPerm_step,butterflyPerm_step,mul_inv_rev,childLift_inv,pairSwitch_inv]
  simp only [mul_assoc]
  rw [←mul_assoc (childLift _),childLift_mul,←mul_assoc (childLift _),childLift_mul]
  congr 2
  apply congrArg childLift
  funext b
  cases b <;> rfl

noncomputable def centralLevelCost (t L : ℕ) : (r : ℕ) →
    (Card r → Equiv.Perm (Card L)) → {ι : Type*} → [Fintype ι] →
    (ι ↪ Card (L+r)) → BenesCoins (L+r) → ℕ
  | 0, _, _, _, _, _ => 0
  | r+1, C, _, _, e, ω =>
    let σ := benesStepEquiv (L+r) ω
    let x := e.trans (headTailEquiv (L+r)).toEmbedding
    let c := PairRouting.colors x σ.2.1
    let hc := PairRouting.colors_compatible x σ.2.1
    if t = L+r+1 then PairRouting.alternatingCycles (PairRouting.switchedEmbedding x σ.2.1)
      (fun b => centralPalindromePerm L r (fun u => C (Fin.cons b u)) (if b then σ.1.2 else σ.1.1))
    else centralLevelCost t L r (fun u => C (Fin.cons false u))
      (PairRouting.childEmbedding x c hc false) σ.1.1 +
      centralLevelCost t L r (fun u => C (Fin.cons true u))
      (PairRouting.childEmbedding x c hc true) σ.1.2

noncomputable def centralSlabCost (l L r : ℕ) (C : Card r → Equiv.Perm (Card L))
    {ι : Type*} [Fintype ι] (e : ι ↪ Card (L+r)) (ω : BenesCoins (L+r)) : ℕ :=
  ∑ i : Fin l, centralLevelCost (l+i.val+1) L r C e ω

lemma permDistance_childLift (d : ℕ) (p q : Bool → Equiv.Perm (Card d)) :
    permDistance (childLift p) (childLift q) =
      permDistance (p false) (q false)+permDistance (p true) (q true) := by
  classical
  rw [permDistance_sum]
  have hh : (∑ x : Card (d+1), if childLift p x = childLift q x then 0 else 1) =
      ∑ x : Bool × Card d, if p x.1 x.2 = q x.1 x.2 then 0 else 1 := by
    apply Fintype.sum_equiv (headTailEquiv d)
    intro x
    have hx : (headTailEquiv d) x = (x 0,Fin.tail x) := rfl
    rw [hx]
    congr 1
    apply propext
    constructor
    · intro h
      have ht := congrArg Fin.tail h
      simpa only [childLift,Equiv.coe_fn_mk,Fin.tail_cons] using ht
    · intro h
      dsimp only [childLift,Equiv.coe_fn_mk]
      exact congrArg (fun z : Card d => (Fin.cons (x 0) z : Card (d+1))) h
  rw [hh]
  simp only [Fintype.sum_prod_type,Fintype.sum_bool,permDistance_sum]
  omega

noncomputable def centralDistance (L r : ℕ) (C D : Card r → Equiv.Perm (Card L)) : ℕ :=
  ∑ u : Card r, permDistance (C u) (D u)

lemma centralDistance_step (L r : ℕ) (C D : Card (r+1) → Equiv.Perm (Card L)) :
    centralDistance L (r+1) C D =
      centralDistance L r (fun u => C (Fin.cons false u)) (fun u => D (Fin.cons false u))+
      centralDistance L r (fun u => C (Fin.cons true u)) (fun u => D (Fin.cons true u)) := by
  classical
  unfold centralDistance
  rw [Fintype.sum_equiv (headTailEquiv r) _
    (fun x : Bool × Card r => permDistance (C (Fin.cons x.1 x.2)) (D (Fin.cons x.1 x.2)))
      (fun x => by
        change permDistance (C x) (D x) =
          permDistance (C (Fin.cons (x 0) (Fin.tail x))) (D (Fin.cons (x 0) (Fin.tail x)))
        rw [Fin.cons_self_tail])]
  simp only [Fintype.sum_prod_type,Fintype.sum_bool]
  omega

lemma permDistance_centralBlock (L r : ℕ) (C D : Card r → Equiv.Perm (Card L)) :
    permDistance (centralBlockPerm L r C) (centralBlockPerm L r D) = centralDistance L r C D := by
  induction r with
  | zero =>
    simp only [centralBlockPerm,centralDistance,Fintype.sum_unique]
    congr 1
  | succ r ih =>
    rw [centralBlockPerm,centralBlockPerm,permDistance_childLift,centralDistance_step,ih,ih]

lemma permDistance_centralPalindrome (L r : ℕ) (C D : Card r → Equiv.Perm (Card L))
    (ω : BenesCoins (L+r)) :
    permDistance (centralPalindromePerm L r C ω) (centralPalindromePerm L r D ω) =
      centralDistance L r C D := by
  rw [centralPalindromePerm,centralPalindromePerm,permDistance_mul_right,
    permDistance_mul_left,permDistance_centralBlock]

lemma centralLevelCost_step (t L r : ℕ) (C : Card (r+1) → Equiv.Perm (Card L))
    {ι : Type*} [Fintype ι] (e : ι ↪ Card (L+r+1))
    (ω : BenesCoins (L+r) × BenesCoins (L+r))
    (coins : (Card (L+r) → Bool) × (Card (L+r) → Bool)) :
    centralLevelCost t L (r+1) C e ((benesStepEquiv (L+r)).symm (ω,coins)) =
      let x := e.trans (headTailEquiv (L+r)).toEmbedding
      let c := PairRouting.colors x coins.1
      let hc := PairRouting.colors_compatible x coins.1
      if t = L+r+1 then PairRouting.alternatingCycles (PairRouting.switchedEmbedding x coins.1)
        (fun b => centralPalindromePerm L r (fun u => C (Fin.cons b u)) (if b then ω.2 else ω.1))
      else centralLevelCost t L r (fun u => C (Fin.cons false u))
        (PairRouting.childEmbedding x c hc false) ω.1 +
        centralLevelCost t L r (fun u => C (Fin.cons true u))
        (PairRouting.childEmbedding x c hc true) ω.2 := by
  rw [centralLevelCost]
  rfl

lemma centralLevelCost_perturb (t L r : ℕ) (C D : Card r → Equiv.Perm (Card L))
    {ι : Type*} [Fintype ι] (e : ι ↪ Card (L+r)) (ω : BenesCoins (L+r)) :
    centralLevelCost t L r C e ω ≤ centralLevelCost t L r D e ω+centralDistance L r C D := by
  induction r generalizing ι with
  | zero => simp only [centralLevelCost,Nat.zero_add,Nat.zero_le]
  | succ r ih =>
    rw [←(benesStepEquiv (L+r)).symm_apply_apply ω,centralLevelCost_step,centralLevelCost_step]
    dsimp only
    split_ifs with ht
    · have hh := alternatingCycles_distance_le
        (PairRouting.switchedEmbedding (e.trans (headTailEquiv (L+r)).toEmbedding)
          (benesStepEquiv (L+r) ω).2.1)
        (fun b => centralPalindromePerm L r (fun u => C (Fin.cons b u))
          (if b then (benesStepEquiv (L+r) ω).1.2 else (benesStepEquiv (L+r) ω).1.1))
        (fun b => centralPalindromePerm L r (fun u => D (Fin.cons b u))
          (if b then (benesStepEquiv (L+r) ω).1.2 else (benesStepEquiv (L+r) ω).1.1))
      simpa only [Bool.false_eq_true,↓reduceIte,permDistance_centralPalindrome,←centralDistance_step] using hh
    · rw [centralDistance_step]
      have h₀ := ih (fun u => C (Fin.cons false u)) (fun u => D (Fin.cons false u))
        (PairRouting.childEmbedding (e.trans (headTailEquiv (L+r)).toEmbedding)
          (PairRouting.colors (e.trans (headTailEquiv (L+r)).toEmbedding) (benesStepEquiv (L+r) ω).2.1)
          (PairRouting.colors_compatible _ _) false)
        (benesStepEquiv (L+r) ω).1.1
      have h₁ := ih (fun u => C (Fin.cons true u)) (fun u => D (Fin.cons true u))
        (PairRouting.childEmbedding (e.trans (headTailEquiv (L+r)).toEmbedding)
          (PairRouting.colors (e.trans (headTailEquiv (L+r)).toEmbedding) (benesStepEquiv (L+r) ω).2.1)
          (PairRouting.colors_compatible _ _) true)
        (benesStepEquiv (L+r) ω).1.2
      omega

lemma centralSlabCost_perturb (l L r : ℕ) (C D : Card r → Equiv.Perm (Card L))
    {ι : Type*} [Fintype ι] (e : ι ↪ Card (L+r)) (ω : BenesCoins (L+r)) :
    centralSlabCost l L r C e ω ≤ centralSlabCost l L r D e ω+l*centralDistance L r C D := by
  have hh := Finset.sum_le_sum (fun (i : Fin l) (_ : i ∈ Finset.univ) =>
    centralLevelCost_perturb (l+i.val+1) L r C D e ω)
  simpa only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,Nat.cast_id,centralSlabCost] using hh

end Thorp

end ThorpNine.SparseSaving

end OAI
