import Mathlib
import OAI.Probability.ThorpRouting.Dense.CutoffMass

namespace OAI

namespace ThorpNine.Dense

namespace Thorp

lemma familyEnd_two (L n : ℕ) : 2*familyEnd L n ≤ L*4^n := by
  cases n with
  | zero => simp [familyEnd]
  | succ n => simp only [familyEnd,Nat.succ_ne_zero,ite_false,Nat.add_one_sub_one,pow_succ]; nlinarith

lemma familyEnd_ge (L n j : ℕ) (hj : j < n) : 2*(L*4^j) ≤ familyEnd L n := by
  cases n with
  | zero => omega
  | succ n =>
    simp only [familyEnd,Nat.succ_ne_zero,ite_false,Nat.add_one_sub_one]
    apply Nat.mul_le_mul_left
    exact Nat.mul_le_mul_left L (Nat.pow_le_pow_right (by decide) (by omega : j ≤ n))

noncomputable def palindromeFamilyCost (L n d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (ω : BenesCoins d) : ℕ :=
  ∑ j ∈ Finset.range n, palindromeSlabCost (L*4^j) d e ω

lemma palindromeFamilyCost_adapted (L n d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (X : SwitchIndex d → Bool) :
    LayerAdapted d (familyEnd L n) (fun Y => palindromeFamilyCost L n d e (Y,X)) := by
  apply layerAdapted_sum
  intro j hj
  exact layerAdapted_mono (palindromeSlabCost_adapted (L*4^j) d e X)
    (familyEnd_ge L n j (Finset.mem_range.mp hj))

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

open scoped BigOperators
namespace Thorp.RoutingNetwork
variable {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]
  {d : ℕ} (R : RoutingNetwork α ι d)

omit [DecidableEq α] in
lemma single_min_eq_within (o : α → Option (Fin 1)) (u v : α) :
    min (pathWeight o u) (pathWeight o v) = withinWeight o u v := by
  cases hu : o u with
  | none =>
    cases hv : o v with
    | none => simp [pathWeight, withinWeight, hu, hv]
    | some j =>
      have hj : 0 ≤ slotWeight o j := by unfold slotWeight; positivity
      simp [pathWeight, withinWeight, hu, hv, min_eq_left hj]
  | some i =>
    cases hv : o v with
    | none =>
      have hi : 0 ≤ slotWeight o i := by unfold slotWeight; positivity
      simp [pathWeight, withinWeight, hu, hv, min_eq_right hi]
    | some j =>
      have hij : i = j := Subsingleton.elim _ _
      simp [pathWeight, withinWeight, hu, hv, hij]

lemma single_rotationCharge_mean_bound {o : α → Option (Fin 1)}
    [∀ i : Fin 1, Nonempty {x : α // o x = some i}]
    (b : ι → Bool) :
    finiteMean (rotationCharge R o b) ≤
      Real.log (cycleFiber o 0).card / Real.log 2 := by
  classical
  have hn : ∀ i, (cycleFiber o i).Nonempty := by
    intro i
    obtain ⟨x,hx⟩ := (inferInstance : Nonempty {x : α // o x = some i})
    exact ⟨x, (mem_cycleFiber _ _ _).mpr hx⟩
  have hm : Monotone (fun i => (cycleFiber o i).card) := by
    intro i j _
    have : i = j := Subsingleton.elim _ _
    simp [this]
  unfold rotationCharge
  rw [finiteMean_sum]
  simp only [rotationMeeting_mean hm, single_min_eq_within, ← two_mul]
  rw [← Finset.mul_sum]
  have h := withinWeight_sum_bound R o hn b
  simp only [Fin.sum_univ_one] at h
  rw [mul_comm 2 (Real.log 2), div_mul_eq_div_div] at h
  linarith

lemma single_rotation_exp_bound {o : α → Option (Fin 1)}
    [∀ i : Fin 1, Nonempty {x : α // o x = some i}]
    (b : ι → Bool) :
    1 / (cycleFiber o 0).card ≤
      finiteMean (fun z : Terminal o => Real.exp (-Real.log 2 * rotationCharge R o b z)) := by
  have h := single_rotationCharge_mean_bound R (o := o) b
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcard : (0 : ℝ) < (cycleFiber o 0).card := by
    apply Nat.cast_pos.mpr
    apply Finset.card_pos.mpr
    obtain ⟨x,hx⟩ := (inferInstance : Nonempty {x : α // o x = some 0})
    exact ⟨x, (mem_cycleFiber _ _ _).mpr hx⟩
  have hm : -Real.log (cycleFiber o 0).card ≤
      finiteMean (fun z : Terminal o => -Real.log 2 * rotationCharge R o b z) := by
    have he := finiteMean_mul_const (rotationCharge R o b) (-Real.log 2)
    simp only [mul_comm] at he
    rw [he]
    have hh := mul_le_mul_of_nonpos_left h (neg_nonpos.mpr hlog.le)
    calc
      _ = -Real.log 2 * (Real.log (cycleFiber o 0).card / Real.log 2) := by
        field_simp
      _ ≤ _ := hh
  have he := (Real.exp_le_exp.mpr hm).trans (exp_finiteMean_le _)
  simpa only [Real.exp_neg, Real.exp_log hcard, one_div] using he

lemma single_collection_rotation_lower (S : Finset α) (r : ℕ)
    (ω : ι → Bool) (c : CycleSlots (R.perm ω) S (fun _ : Fin 1 => r)) :
    (2:ℝ)^d ≤ ∑ z : Terminal c.val,
      (2:ℝ)^d * Real.exp (-Real.log 2 * rotationCharge R c.val ω z) := by
  classical
  let (i : Fin 1) : Nonempty {x : α // c.val x = some i} := c.terminal_nonempty i
  have hb := single_rotation_exp_bound R ω (o := c.val)
  have hcard : (Fintype.card (Terminal c.val) : ℝ) = (cycleFiber c.val 0).card := by
    rw [Fintype.card_pi]
    simp only [Fin.prod_univ_one, card_cycleFiber]
  have hp : (0:ℝ) < Fintype.card (Terminal c.val) := Nat.cast_pos.mpr Fintype.card_pos
  have hh := (le_div_iff₀ hp).mp hb
  rw [hcard, one_div_mul_cancel (ne_of_gt (by simpa only [hcard] using hp))] at hh
  rw [← Finset.mul_sum]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hh (show 0 ≤ (2:ℝ)^d by positivity)

lemma single_cycleSlots_weighted_moment (S : Finset α) (r : ℕ) :
    finiteMean (fun ω : ι → Bool =>
      (Fintype.card (CycleSlots (R.perm ω) S (fun _ : Fin 1 => r)) : ℝ)) *
      (2:ℝ)^d ≤ S.card := by
  classical
  let rs : Fin 1 → ℕ := fun _ => r
  let g (a : Fin 1 → S) (ω : ι → Bool) : ℝ :=
    if (QueryTree.seekCycles R S (List.ofFn (fun i => ((a i).val,rs i))) ∅).succeeds ω then
      ((2:ℝ)^d)^1 / (2:ℝ)^(QueryTree.seekCycles R S (List.ofFn (fun i => ((a i).val,rs i))) ∅).staleCharge ∅ ω
    else 0
  have hω (ω : ι → Bool) :
      (Fintype.card (CycleSlots (R.perm ω) S rs) : ℝ) * (2:ℝ)^d ≤
        ∑ a : Fin 1 → S, g a ω := by
    calc
      _ = ∑ _c : CycleSlots (R.perm ω) S rs, (2:ℝ)^d := by simp
      _ ≤ ∑ c : CycleSlots (R.perm ω) S rs,
          ∑ z : Terminal c.val, ((2:ℝ)^d)^1 * Real.exp (-Real.log 2 * rotationCharge R c.val ω z) := by
        apply Finset.sum_le_sum
        intro c _
        simpa only [pow_one] using single_collection_rotation_lower R S r ω c
      _ = ∑ c : RootedSlots (R.perm ω) S rs,
          ((2:ℝ)^d)^1 * Real.exp (-Real.log 2 * rotationCharge R c.1.val ω c.2) :=
        (Fintype.sum_sigma (fun c : RootedSlots (R.perm ω) S rs =>
          ((2:ℝ)^d)^1 * Real.exp (-Real.log 2 * rotationCharge R c.1.val ω c.2))).symm
      _ ≤ _ := rooted_weight_sum_le R S rs ω
  have hb := finiteMean_mono hω
  rw [finiteMean_mul_const, finiteMean_sum] at hb
  calc
    _ ≤ ∑ a : Fin 1 → S, finiteMean (g a) := hb
    _ ≤ ∑ _a : Fin 1 → S, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro a _
      have hh := QueryTree.cycles_weighted_success R S (List.ofFn (fun i : Fin 1 => ((a i).val,rs i)))
      simpa only [List.length_ofFn] using hh
    _ = _ := by simp

noncomputable def singleRootedEquiv (p : Equiv.Perm α) (r : ℕ) :
    RootedSlots p Finset.univ (fun _ : Fin 1 => r) ≃
      {x : α // (orbitSet p x).card = r + 1} := by
  classical
  let f : RootedSlots p Finset.univ (fun _ : Fin 1 => r) →
      {x : α // (orbitSet p x).card = r + 1} := fun c =>
    ⟨(c.2 0).val, by rw [c.1.property.2.2 0 _ (c.2 0).property, c.1.property.1]⟩
  apply Equiv.ofBijective f
  constructor
  · intro c c' h
    apply rootedStart_injective
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    apply Subtype.ext
    exact congrArg p (congrArg Subtype.val h)
  · intro x
    let C : SelectedCycle p Finset.univ := ⟨orbitSet p x, ⟨⟨x,rfl⟩, Finset.subset_univ _⟩⟩
    let a : SlotAssignment p Finset.univ (fun _ : Fin 1 => r) :=
      ⟨fun _ => C, Function.injective_of_subsingleton _, fun _ => x.property⟩
    let c := assignmentToSlots a
    have hx : ∀ i : Fin 1, c.val x = some i := by
      intro i
      change assignmentOwner a x = some i
      rw [assignmentOwner_eq_some]
      exact (mem_orbitSet _ _ _).mpr (Equiv.Perm.SameCycle.refl p x)
    exact ⟨⟨c, fun i => ⟨x, hx i⟩⟩, Subtype.ext rfl⟩

lemma single_root_count (p : Equiv.Perm α) (r : ℕ) :
    (Fintype.card {x : α // (orbitSet p x).card = r+1} : ℝ) =
      (Fintype.card (CycleSlots p Finset.univ (fun _ : Fin 1 => r)) : ℝ) * (r+1) := by
  classical
  rw [← Fintype.card_congr (singleRootedEquiv p r), Fintype.card_sigma]
  simp only [Fintype.card_pi, Fin.prod_univ_one, card_cycleFiber]
  simp only [Nat.cast_sum]
  have he (c : CycleSlots p Finset.univ (fun _ : Fin 1 => r)) :
      ((cycleFiber c.val 0).card : ℝ) = (r : ℝ) + 1 := by
    rw [c.property.1]; norm_cast
  simp only [he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

lemma uniform_cycle_length_cap [Nonempty α] (r : ℕ) :
    finiteMean (fun ω : ι → Bool => finiteMean (fun x : α =>
      if (orbitSet (R.perm ω) x).card = r+1 then (1:ℝ) else 0)) ≤
      ((r : ℝ)+1) / (2:ℝ)^d := by
  classical
  have hn : 0 < (Fintype.card α : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hinner (ω : ι → Bool) :
      finiteMean (fun x : α => if (orbitSet (R.perm ω) x).card = r+1 then (1:ℝ) else 0) =
        (Fintype.card (CycleSlots (R.perm ω) Finset.univ (fun _ : Fin 1 => r)) : ℝ) *
          (((r:ℝ)+1) / Fintype.card α) := by
    rw [← mul_div_assoc, ← single_root_count (R.perm ω) r]
    simp [finiteMean, Fintype.card_subtype]
  simp only [hinner, finiteMean_mul_const]
  have h := single_cycleSlots_weighted_moment R Finset.univ r
  simp only [Finset.card_univ] at h
  have h' := (le_div_iff₀ (show 0 < (2:ℝ)^d by positivity)).mpr h
  calc
    _ ≤ ((Fintype.card α : ℝ) / (2:ℝ)^d) * (((r:ℝ)+1) / Fintype.card α) :=
      mul_le_mul_of_nonneg_right h' (by positivity)
    _ = _ := by field_simp

end Thorp.RoutingNetwork


namespace Thorp.DenseTruncation
open scoped BigOperators

lemma law_reciprocal_summable {j : ℕ} {p : ℕ → ℝ}
    (hp : AdmissibleCycleLaw j p) :
    Summable (fun l => p l / ((l + 1 : ℕ) : ℝ)) := by
  apply Summable.of_nonneg_of_le (fun l => div_nonneg (hp.1 l) (by positivity))
    (fun l => ?_) hp.2.1.summable
  exact div_le_self (hp.1 l) (by exact_mod_cast Nat.succ_pos l)

lemma law_reciprocal_nonneg {j : ℕ} {p : ℕ → ℝ}
    (hp : AdmissibleCycleLaw j p) :
    0 ≤ ∑' l : ℕ, p l / ((l + 1 : ℕ) : ℝ) :=
  tsum_nonneg (fun l => div_nonneg (hp.1 l) (by positivity))

lemma law_reciprocal_le_one {j : ℕ} {p : ℕ → ℝ}
    (hp : AdmissibleCycleLaw j p) :
    (∑' l : ℕ, p l / ((l + 1 : ℕ) : ℝ)) ≤ 1 := by
  rw [← hp.2.1.tsum_eq]
  exact Summable.tsum_le_tsum (fun l => div_le_self (hp.1 l)
    (by exact_mod_cast Nat.succ_pos l)) (law_reciprocal_summable hp) hp.2.1.summable

lemma reciprocal_values_bdd (j : ℕ) : BddAbove
    {z : ℝ | ∃ p : ℕ → ℝ, AdmissibleCycleLaw j p ∧
      z = ∑' l : ℕ, p l / ((l + 1 : ℕ) : ℝ)} :=
  ⟨1, fun _ ⟨_,hp,hz⟩ => hz ▸ law_reciprocal_le_one hp⟩

lemma reciprocal_le_h {j : ℕ} {p : ℕ → ℝ}
    (hp : AdmissibleCycleLaw j p) :
    (∑' l : ℕ, p l / ((l + 1 : ℕ) : ℝ)) ≤ h j :=
  le_csSup (reciprocal_values_bdd j) ⟨p,hp,rfl⟩

lemma subprob_reciprocal_le_h {j : ℕ} {q : ℕ → ℝ}
    (hq : ∀ l, 0 ≤ q l) (hs : Summable q) (ht : (∑' l, q l) ≤ 1)
    (hc : ∀ l, q l ≤ ((l+1 : ℕ) : ℝ) / (2:ℝ)^(j-1)) :
    (∑' l, q l / ((l+1 : ℕ) : ℝ)) ≤ h j := by
  let t := 2^(j-1)-1
  have hpow : 1 ≤ 2^(j-1) := Nat.one_le_pow _ _ (by norm_num)
  have htlen : (t+1 : ℕ) = 2^(j-1) := Nat.sub_add_cancel hpow
  have hreal : ((t+1 : ℕ) : ℝ) = (2:ℝ)^(j-1) := by rw [htlen]; norm_cast
  let m := 1 - ∑' l, q l
  have hm : 0 ≤ m := sub_nonneg.mpr ht
  let a : ℕ → ℝ := fun l => if l=t then m else 0
  have ha : HasSum a m := by
    simpa only [a,ite_eq_left rfl] using (hasSum_single t (f := a) (fun l hl => by simp [a,hl]))
  let p : ℕ → ℝ := fun l => q l+a l
  have hp : AdmissibleCycleLaw j p := by
    refine ⟨fun l => add_nonneg (hq l) (by dsimp [a]; split_ifs <;> positivity), ?_, ?_⟩
    · convert hs.hasSum.add ha using 1; dsimp [p,m]; ring
    · intro l
      by_cases hl : l=t
      · subst l
        have hqt := hs.le_tsum t (fun l _ => hq l)
        have hp2 : (2:ℝ)^(j-1) ≠ 0 := by positivity
        simp only [p,a,hreal,div_self hp2]
        dsimp [m]
        linarith
      · simpa only [p,a,ite_eq_right hl,add_zero] using hc l
  have hqs : Summable (fun l => q l / ((l+1 : ℕ) : ℝ)) := by
    apply Summable.of_nonneg_of_le (fun l => div_nonneg (hq l) (by positivity))
      (fun l => div_le_self (hq l) (by exact_mod_cast Nat.succ_pos l)) hs
  calc
    _ ≤ ∑' l, p l / ((l+1 : ℕ) : ℝ) := by
      apply Summable.tsum_le_tsum _ hqs (law_reciprocal_summable hp)
      intro l
      apply div_le_div_of_nonneg_right _ (by positivity)
      dsimp [p,a]
      split_ifs <;> linarith
    _ ≤ _ := reciprocal_le_h hp

end Thorp.DenseTruncation


end ThorpNine.Dense

end OAI
