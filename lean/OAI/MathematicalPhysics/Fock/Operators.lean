import OAI.InformationTheory.PhotonNumber.Basic
import OAI.Analysis.QuantumTrace.Basic

namespace OAI

noncomputable section

section
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate

namespace WeightedShift
variable {I J : Type*}
abbrev H (I : Type*) := lp (fun _ : I => ℂ) 2

theorem hasSum_square (x : H I) : HasSum (fun i => ‖x i‖^2) (‖x‖^2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using lp.hasSum_norm (p := 2) (by norm_num) x

theorem pull_mem (f : I → J) (hf : Function.Injective f) (c : I → ℂ)
    (C : ℝ) (_hC : 0 ≤ C) (hc : ∀ i, ‖c i‖ ≤ C) (x : H J) :
    Memℓp (fun i => c i*x (f i)) 2 := by
  apply (memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)).mpr
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  apply (((hasSum_square x).summable.comp_injective hf).mul_left (C^2)).of_nonneg_of_le
    (fun _ => sq_nonneg _)
  intro i
  rw [norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hc i) 2) (sq_nonneg _)

def pull (f : I → J) (hf : Function.Injective f) (c : I → ℂ)
    (C : ℝ) (hC : 0 ≤ C) (hc : ∀ i, ‖c i‖ ≤ C) (x : H J) : H I :=
  ⟨_, pull_mem f hf c C hC hc x⟩
@[simp] theorem pull_apply (f : I → J) (hf : Function.Injective f) (c : I → ℂ)
    (C : ℝ) (hC : 0 ≤ C) (hc : ∀ i, ‖c i‖ ≤ C) (x : H J) (i : I) :
    pull f hf c C hC hc x i = c i*x (f i) := rfl

theorem pull_bound (f : I → J) (hf : Function.Injective f) (c : I → ℂ)
    (C : ℝ) (hC : 0 ≤ C) (hc : ∀ i, ‖c i‖ ≤ C) (x : H J) :
    ‖pull f hf c C hC hc x‖ ≤ C*‖x‖ := by
  have h₁ : ‖pull f hf c C hC hc x‖^2 ≤ C^2*∑' i, ‖x (f i)‖^2 := by
    rw [← (hasSum_square (pull f hf c C hC hc x)).tsum_eq, ← tsum_mul_left]
    apply Summable.tsum_le_tsum (fun i => ?_) (hasSum_square _).summable
      (((hasSum_square x).summable.comp_injective hf).mul_left _)
    simp only [pull_apply, norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hc i) 2) (sq_nonneg _)
  have h₂ : (∑' i, ‖x (f i)‖^2) ≤ ‖x‖^2 := by
    rw [← (hasSum_square x).tsum_eq]
    exact tsum_comp_le_tsum_of_inj (hasSum_square x).summable (fun _ => sq_nonneg _) hf
  have h₃ := mul_le_mul_of_nonneg_left h₂ (sq_nonneg C)
  nlinarith [norm_nonneg (pull f hf c C hC hc x), mul_nonneg hC (norm_nonneg x)]

def pullCLM (f : I → J) (hf : Function.Injective f) (c : I → ℂ)
    (C : ℝ) (hC : 0 ≤ C) (hc : ∀ i, ‖c i‖ ≤ C) : H J →L[ℂ] H I :=
  LinearMap.mkContinuous
    { toFun := pull f hf c C hC hc
      map_add' := fun x y => by
        apply lp.ext
        funext i
        change c i*(x (f i)+y (f i)) = c i*x (f i)+c i*y (f i)
        ring
      map_smul' := fun z x => by
        apply lp.ext
        funext i
        change c i*(z*x (f i)) = z*(c i*x (f i))
        ring }
    C (pull_bound f hf c C hC hc)
@[simp] theorem pullCLM_apply (f : I → J) (hf : Function.Injective f) (c : I → ℂ)
    (C : ℝ) (hC : 0 ≤ C) (hc : ∀ i, ‖c i‖ ≤ C) (x : H J) (i : I) :
    pullCLM f hf c C hC hc x i = c i*x (f i) := rfl

variable [DecidableEq I] [DecidableEq J]

theorem pullCLM_single (f : I → J) (hf : Function.Injective f) (c : I → ℂ)
    (C : ℝ) (hC : 0 ≤ C) (hc : ∀ i, ‖c i‖ ≤ C) (i : I) (z : ℂ) :
    pullCLM f hf c C hC hc (lp.single 2 (f i) z) = lp.single 2 i (c i*z) := by
  apply lp.ext
  funext k
  simp only [pullCLM_apply, lp.coeFn_single, Pi.single_apply]
  by_cases he : k = i
  · subst k; simp
  · have hh : f k ≠ f i := fun h => he (hf h)
    simp [he, hh]

omit [DecidableEq I] in
 theorem pullCLM_single_outside (f : I → J) (hf : Function.Injective f) (c : I → ℂ)
    (C : ℝ) (hC : 0 ≤ C) (hc : ∀ i, ‖c i‖ ≤ C) (j : J) (hj : ∀ i, f i ≠ j) (z : ℂ) :
    pullCLM f hf c C hC hc (lp.single 2 j z) = 0 := by
  apply lp.ext
  funext i
  simp [hj i]

 theorem adjoint_apply_image (f : I → J) (hf : Function.Injective f) (c : I → ℂ)
    (C : ℝ) (hC : 0 ≤ C) (hc : ∀ i, ‖c i‖ ≤ C) (x : H I) (i : I) :
    (pullCLM f hf c C hC hc).adjoint x (f i) = conj (c i)*x i := by
  have hh := ContinuousLinearMap.adjoint_inner_right (pullCLM f hf c C hC hc)
    (lp.single 2 (f i) 1) x
  simpa only [pullCLM_single, mul_one, lp.inner_single_left, RCLike.inner_apply,
    map_one, one_mul, mul_comm] using hh

omit [DecidableEq I] in
 theorem adjoint_apply_outside (f : I → J) (hf : Function.Injective f) (c : I → ℂ)
    (C : ℝ) (hC : 0 ≤ C) (hc : ∀ i, ‖c i‖ ≤ C) (x : H I) (j : J) (hj : ∀ i, f i ≠ j) :
    (pullCLM f hf c C hC hc).adjoint x j = 0 := by
  have hh := ContinuousLinearMap.adjoint_inner_right (pullCLM f hf c C hC hc)
    (lp.single 2 j 1) x
  rw [pullCLM_single_outside f hf c C hC hc j hj, inner_zero_left] at hh
  simpa only [lp.inner_single_left, RCLike.inner_apply, map_one, mul_one] using hh

end WeightedShift

namespace Annihilation
open EntropyPhotonNumber QuantumTrace
variable {n : ℕ}

def up (j : Fin n) (k : NumberIndex n) : NumberIndex n := k + Pi.single j 1
@[simp] theorem up_same (j : Fin n) (k : NumberIndex n) : up j k j = k j+1 := by simp [up]
@[simp] theorem up_other (j l : Fin n) (hl : l ≠ j) (k : NumberIndex n) : up j k l = k l := by simp [up, Pi.single_eq_of_ne hl]
theorem up_injective (j : Fin n) : Function.Injective (up j) := by
  intro k l h
  exact add_right_cancel h
@[simp] theorem weight_up (j : Fin n) (k : NumberIndex n) : numberWeight (up j k) = numberWeight k+1 := by
  simp only [numberWeight, up, Pi.add_apply, Nat.cast_add, Finset.sum_add_distrib]
  have h : (∑ i : Fin n, (((Pi.single j 1 : Fin n → ℕ) i): ℝ)) = 1 := by
    simp only [Pi.single_apply]
    simp
  rw [h]
  ring

theorem coordinate_le_weight (j : Fin n) (k : NumberIndex n) : (k j:ℝ)+1 ≤ numberWeight k := by
  have h : (k j:ℝ) ≤ ∑ i : Fin n, (k i:ℝ) :=
    Finset.single_le_sum (fun i _ => Nat.cast_nonneg (k i)) (Finset.mem_univ j)
  dsimp [numberWeight]
  linarith

theorem sqrt_step_le_weight (j : Fin n) (k : NumberIndex n) : Real.sqrt ((k j:ℝ)+1) ≤ numberWeight (up j k) := by
  have h₁ := coordinate_le_weight j k
  have h₂ := numberWeight_one_le k
  have hs := Real.sq_sqrt (show 0 ≤ (k j:ℝ)+1 by positivity)
  have hp := Real.sqrt_nonneg ((k j:ℝ)+1)
  rw [weight_up]
  nlinarith

def coefficient (a b : ℕ) (j : Fin n) (k : NumberIndex n) : ℂ :=
  ((numberWeight k)^a*Real.sqrt ((k j:ℝ)+1)/(numberWeight (up j k))^b : ℝ)

theorem coefficient_bound (a b : ℕ) (hab : a+1 ≤ b) (j : Fin n) (k : NumberIndex n) : ‖coefficient a b j k‖ ≤ 1 := by
  have hk := numberWeight_one_le k
  have hu := numberWeight_one_le (up j k)
  have hkpos : 0 < numberWeight k := by linarith
  have hupos : 0 < numberWeight (up j k) := by linarith
  have hm : numberWeight k ≤ numberWeight (up j k) := by rw [weight_up]; linarith
  have hp : numberWeight k^a*Real.sqrt ((k j:ℝ)+1) ≤ numberWeight (up j k)^(a+1) := by
    rw [pow_succ]
    exact mul_le_mul (pow_le_pow_left₀ hkpos.le hm a) (sqrt_step_le_weight j k)
      (Real.sqrt_nonneg _) (pow_nonneg hupos.le _)
  have hpow : numberWeight (up j k)^(a+1) ≤ numberWeight (up j k)^b :=
    pow_le_pow_right₀ hu hab
  rw [coefficient, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact (div_le_one (pow_pos hupos b)).mpr (hp.trans hpow)


def sandwich (a b : ℕ) (hab : a+1 ≤ b) (j : Fin n) : Fock n →L[ℂ] Fock n :=
  WeightedShift.pullCLM (up j) (up_injective j) (coefficient a b j) 1 (by norm_num)
    (coefficient_bound a b hab j)
@[simp] theorem sandwich_apply (a b : ℕ) (hab : a+1 ≤ b) (j : Fin n) (x : Fock n) (k : NumberIndex n) :
    sandwich a b hab j x k = coefficient a b j k*x (up j k) := rfl

theorem sandwich_norm_le (a b : ℕ) (hab : a+1 ≤ b) (j : Fin n) : ‖sandwich a b hab j‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  exact WeightedShift.pull_bound (up j) (up_injective j) _ 1 (by norm_num) (coefficient_bound a b hab j) x

end Annihilation

namespace Annihilation
open EntropyPhotonNumber QuantumTrace
open scoped ComplexConjugate
variable {n : ℕ}

theorem sqrt_step_le_base (j : Fin n) (k : NumberIndex n) : Real.sqrt ((k j:ℝ)+1) ≤ numberWeight k := by
  have h₁ := coordinate_le_weight j k
  have h₂ := numberWeight_one_le k
  have hs := Real.sq_sqrt (show 0 ≤ (k j:ℝ)+1 by positivity)
  nlinarith [Real.sqrt_nonneg ((k j:ℝ)+1)]

def creationCoefficient (a b : ℕ) (j : Fin n) (k : NumberIndex n) : ℂ :=
  ((numberWeight (up j k))^a*Real.sqrt ((k j:ℝ)+1)/(numberWeight k)^b : ℝ)

theorem creationCoefficient_bound (a b : ℕ) (hab : a+1 ≤ b) (j : Fin n) (k : NumberIndex n) :
    ‖creationCoefficient a b j k‖ ≤ 2^a := by
  have hk := numberWeight_one_le k
  have hkpos : 0 < numberWeight k := by linarith
  have hu : 0 < numberWeight (up j k) := by linarith [numberWeight_one_le (up j k)]
  have hup : numberWeight (up j k) ≤ 2*numberWeight k := by rw [weight_up]; linarith
  have hp : numberWeight (up j k)^a*Real.sqrt ((k j:ℝ)+1) ≤ 2^a*numberWeight k^(a+1) := by
    calc
      _ ≤ (2*numberWeight k)^a*numberWeight k := mul_le_mul
        (pow_le_pow_left₀ (by linarith [numberWeight_one_le (up j k)]) hup a)
        (sqrt_step_le_base j k) (Real.sqrt_nonneg _) (by positivity)
      _ = _ := by rw [mul_pow, pow_succ]; ring
  have hpow := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hk hab) (show (0:ℝ) ≤ 2^a by positivity)
  rw [creationCoefficient, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact (div_le_iff₀ (pow_pos hkpos b)).mpr (hp.trans hpow)


def creationSandwich (a b : ℕ) (hab : a+1 ≤ b) (j : Fin n) : Fock n →L[ℂ] Fock n :=
  (WeightedShift.pullCLM (up j) (up_injective j) (creationCoefficient a b j) (2^a)
    (by positivity) (creationCoefficient_bound a b hab j)).adjoint

theorem creationSandwich_norm_le (a b : ℕ) (hab : a+1 ≤ b) (j : Fin n) :
    ‖creationSandwich a b hab j‖ ≤ 2^a := by
  rw [creationSandwich, LinearIsometryEquiv.norm_map]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  exact WeightedShift.pull_bound (up j) (up_injective j) _ _ (by positivity) (creationCoefficient_bound a b hab j) x

@[simp] theorem creationSandwich_up (a b : ℕ) (hab : a+1 ≤ b) (j : Fin n) (x : Fock n) (k : NumberIndex n) :
    creationSandwich a b hab j x (up j k) = creationCoefficient a b j k*x k := by
  rw [creationSandwich, WeightedShift.adjoint_apply_image]
  simp only [creationCoefficient, Complex.conj_ofReal]

@[simp] theorem creationSandwich_zero (a b : ℕ) (hab : a+1 ≤ b) (j : Fin n) (x : Fock n)
    (k : NumberIndex n) (hk : k j = 0) : creationSandwich a b hab j x k = 0 := by
  rw [creationSandwich]
  apply WeightedShift.adjoint_apply_outside
  intro l hl
  have hh := congrFun hl j
  rw [up_same, hk] at hh
  omega

def down (j : Fin n) (k : NumberIndex n) : NumberIndex n := Function.update k j (k j-1)
@[simp] theorem up_down (j : Fin n) (k : NumberIndex n) (hk : 0 < k j) : up j (down j k) = k := by
  funext i
  by_cases he : i = j
  · subst i; simp [down, Nat.sub_add_cancel hk]
  · simp [down, he]
@[simp] theorem down_up (j : Fin n) (k : NumberIndex n) : down j (up j k) = k := by
  funext i
  by_cases he : i = j
  · subst i; simp [down]
  · simp [down, he]

 theorem index_cases (j : Fin n) (k : NumberIndex n) : k j = 0 ∨ ∃ l, k = up j l := by
  by_cases hk : k j = 0
  · exact Or.inl hk
  · exact Or.inr ⟨down j k, (up_down j k (Nat.pos_of_ne_zero hk)).symm⟩

 theorem coefficient_inverse_bound (m : ℕ) (k : NumberIndex n) : ‖((numberWeight k^m)⁻¹ : ℂ)‖ ≤ 1 := by
  rw [norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [numberWeight_one_le k])]
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (numberWeight_one_le k))

def inverseWeight (m : ℕ) : Fock n →L[ℂ] Fock n :=
  WeightedShift.pullCLM id Function.injective_id (fun k => ((numberWeight k^m)⁻¹ : ℂ)) 1 (by norm_num)
    (coefficient_inverse_bound m)
@[simp] theorem inverseWeight_apply (m : ℕ) (x : Fock n) (k : NumberIndex n) :
    inverseWeight m x k = ((numberWeight k^m)⁻¹ : ℂ)*x k := rfl

theorem inverseWeight_injective (m : ℕ) : Function.Injective (inverseWeight (n := n) m) := by
  intro x y h
  apply lp.ext
  funext k
  have hh := congrArg (fun z : Fock n => z k) h
  simp only [inverseWeight_apply] at hh
  exact mul_left_cancel₀ (by exact inv_ne_zero (pow_ne_zero m (by exact_mod_cast (show numberWeight k ≠ 0 by linarith [numberWeight_one_le k])))) hh

theorem inverseWeight_add (a b : ℕ) : inverseWeight (n := n) (a+b) = inverseWeight a ∘L inverseWeight b := by
  ext x k
  simp only [inverseWeight_apply, ContinuousLinearMap.comp_apply, pow_add, mul_inv_rev]
  ring

 theorem sandwich_factor (a b : ℕ) (hab : a+1 ≤ b) (j : Fin n) :
    sandwich 0 b (by omega) j = inverseWeight a ∘L sandwich a b hab j := by
  ext x k
  have hn : (numberWeight k : ℂ) ≠ 0 := by exact_mod_cast (show numberWeight k ≠ 0 by linarith [numberWeight_one_le k])
  simp only [ContinuousLinearMap.comp_apply, inverseWeight_apply, sandwich_apply, coefficient,
    pow_zero, one_mul, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow]
  field_simp

 theorem creationSandwich_factor (a b : ℕ) (hab : a+1 ≤ b) (j : Fin n) :
    creationSandwich 0 b (by omega) j = inverseWeight a ∘L creationSandwich a b hab j := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext k
  rcases index_cases j k with hk | ⟨l,rfl⟩
  · simp [creationSandwich_zero _ _ _ _ _ k hk]
  · have hn : (numberWeight (up j l) : ℂ) ≠ 0 := by exact_mod_cast (show numberWeight (up j l) ≠ 0 by linarith [numberWeight_one_le (up j l)])
    simp only [ContinuousLinearMap.comp_apply, inverseWeight_apply, creationSandwich_up, creationCoefficient,
      pow_zero, one_mul, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow]
    field_simp

end Annihilation

namespace Annihilation
open EntropyPhotonNumber QuantumTrace
variable {n : ℕ}

def lowering (j : Fin n) : Fock n →L[ℂ] Fock n := sandwich 0 1 (by omega) j
def raising (j : Fin n) : Fock n →L[ℂ] Fock n := creationSandwich 0 1 (by omega) j

@[simp] theorem lowering_apply (j : Fin n) (x : Fock n) (k : NumberIndex n) :
    lowering j x k = (Real.sqrt ((k j:ℝ)+1) : ℂ)*inverseWeight 1 x (up j k) := by
  simp only [lowering, sandwich_apply, coefficient, pow_zero, one_mul, pow_one,
    Complex.ofReal_div, inverseWeight_apply]
  ring

@[simp] theorem raising_up (j : Fin n) (x : Fock n) (k : NumberIndex n) :
    raising j x (up j k) = (Real.sqrt ((k j:ℝ)+1) : ℂ)*inverseWeight 1 x k := by
  simp only [raising, creationSandwich_up, creationCoefficient, pow_zero, one_mul,
    pow_one, Complex.ofReal_div, inverseWeight_apply]
  ring

@[simp] theorem raising_zero (j : Fin n) (x : Fock n) (k : NumberIndex n) (hk : k j = 0) :
    raising j x k = 0 := creationSandwich_zero _ _ _ _ _ _ hk

 theorem lowering_sq (j : Fin n) (x : Fock n) (k : NumberIndex n) :
    ‖lowering j x k‖^2 = ((k j:ℝ)+1)*‖inverseWeight 1 x (up j k)‖^2 := by
  rw [lowering_apply, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (by positivity)]

 theorem raising_sq (j : Fin n) (x : Fock n) (k : NumberIndex n) :
    ‖raising j x (up j k)‖^2 = ((k j:ℝ)+1)*‖inverseWeight 1 x k‖^2 := by
  rw [raising_up, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (by positivity)]

 theorem lowering_norm_sum (j : Fin n) (x : Fock n) :
    HasSum (fun k : NumberIndex n => (k j:ℝ)*‖inverseWeight 1 x k‖^2) (‖lowering j x‖^2) := by
  have hh := WeightedShift.hasSum_square (lowering j x)
  simp only [lowering_sq] at hh
  have hz (k : NumberIndex n) (hk : k ∉ Set.range (up j)) :
      (k j:ℝ)*‖inverseWeight 1 x k‖^2 = 0 := by
    rcases index_cases j k with he | ⟨l,rfl⟩
    · simp [he]
    · exact (hk ⟨l,rfl⟩).elim
  apply (up_injective j).hasSum_iff hz |>.mp
  simpa only [Function.comp_def, up_same, Nat.cast_add, Nat.cast_one] using hh

 theorem raising_norm_sum (j : Fin n) (x : Fock n) :
    HasSum (fun k : NumberIndex n => ((k j:ℝ)+1)*‖inverseWeight 1 x k‖^2) (‖raising j x‖^2) := by
  have hz (k : NumberIndex n) (hk : k ∉ Set.range (up j)) : ‖raising j x k‖^2 = 0 := by
    rcases index_cases j k with he | ⟨l,rfl⟩
    · simp [raising_zero _ _ _ he]
    · exact (hk ⟨l,rfl⟩).elim
  have hh := (up_injective j).hasSum_iff hz |>.mpr (WeightedShift.hasSum_square (raising j x))
  simpa only [Function.comp_def, raising_sq] using hh


 theorem canonical_norm_identity (j : Fin n) (x : Fock n) :
    ‖raising j x‖^2 = ‖lowering j x‖^2+‖inverseWeight 1 x‖^2 := by
  have hh := (lowering_norm_sum j x).add (WeightedShift.hasSum_square (inverseWeight 1 x))
  have he : HasSum (fun k : NumberIndex n => ((k j:ℝ)+1)*‖inverseWeight 1 x k‖^2)
      (‖lowering j x‖^2+‖inverseWeight 1 x‖^2) := by
    convert! hh using 1
    ext k
    ring
  exact (raising_norm_sum j x).unique he

 theorem inverseWeight_selfAdjoint (m : ℕ) : IsSelfAdjoint (inverseWeight (n := n) m) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  apply HasSum.unique (lp.hasSum_inner (𝕜 := ℂ) (inverseWeight m x) y)
  convert! lp.hasSum_inner (𝕜 := ℂ) x (inverseWeight m y) using 1
  ext k
  simp only [inverseWeight_apply, RCLike.inner_apply, map_mul, map_inv₀, map_pow,
    Complex.conj_ofReal]
  ring

 theorem lowering_adjoint_inverse (j : Fin n) :
    (lowering j).adjoint ∘L inverseWeight 1 = inverseWeight 1 ∘L raising j := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext k
  rcases index_cases j k with hk | ⟨l,rfl⟩
  · have hn : ∀ l, up j l ≠ k := by intro l he; have hh := congrFun he j; rw [up_same, hk] at hh; omega
    change (lowering j).adjoint (inverseWeight 1 x) k = inverseWeight 1 (raising j x) k
    have hh := WeightedShift.adjoint_apply_outside (up j) (up_injective j) (coefficient 0 1 j) 1 (by norm_num) (coefficient_bound 0 1 (by omega) j) (inverseWeight 1 x) k hn
    change (lowering j).adjoint (inverseWeight 1 x) k = 0 at hh
    rw [hh]
    simp [inverseWeight_apply, raising_zero _ _ _ hk]
  · change (lowering j).adjoint (inverseWeight 1 x) (up j l) = inverseWeight 1 (raising j x) (up j l)
    have hh := WeightedShift.adjoint_apply_image (up j) (up_injective j) (coefficient 0 1 j) 1 (by norm_num) (coefficient_bound 0 1 (by omega) j) (inverseWeight 1 x) l
    change (lowering j).adjoint (inverseWeight 1 x) (up j l) = _ at hh
    rw [hh]
    have hc : (starRingEnd ℂ) (coefficient 0 1 j l) = coefficient 0 1 j l :=
      Complex.conj_ofReal _
    rw [hc]
    simp only [coefficient, pow_zero, one_mul, pow_one,
      raising_up, inverseWeight_apply, Complex.ofReal_div]
    ring

 theorem ladder_adjoint_pairing (j : Fin n) (x y : Fock n) :
    inner ℂ (lowering j x) (inverseWeight 1 y) = inner ℂ (inverseWeight 1 x) (raising j y) := by
  rw [← ContinuousLinearMap.adjoint_inner_right]
  have hh := congrArg (fun T : Fock n →L[ℂ] Fock n => T y) (lowering_adjoint_inverse j)
  change (lowering j).adjoint (inverseWeight 1 y) = inverseWeight 1 (raising j y) at hh
  rw [hh]
  exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (inverseWeight_selfAdjoint 1) x (raising j y)).symm

end Annihilation

namespace CrossEnsemble
variable {I J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def operator (u v : I → E) : E →L[ℂ] E := ∑' i, InnerProductSpace.rankOne ℂ (u i) (v i)

omit [InnerProductSpace ℂ E] [CompleteSpace E] in
theorem norm_product_summable {u v : I → E} (hu : Summable (fun i => ‖u i‖^2))
    (hv : Summable (fun i => ‖v i‖^2)) : Summable (fun i => ‖u i‖*‖v i‖) := by
  apply Summable.of_nonneg_of_le (fun i => mul_nonneg (norm_nonneg _) (norm_nonneg _)) _ (hu.add hv)
  intro i
  nlinarith [sq_nonneg (‖u i‖-‖v i‖)]

theorem hasSum_operator {u v : I → E} (hu : Summable (fun i => ‖u i‖^2))
    (hv : Summable (fun i => ‖v i‖^2)) :
    HasSum (fun i => InnerProductSpace.rankOne ℂ (u i) (v i)) (operator u v) := by
  apply Summable.hasSum
  apply Summable.of_norm
  simpa only [InnerProductSpace.norm_rankOne] using norm_product_summable hu hv

theorem entry_hasSum {u v : I → E} (hu : Summable (fun i => ‖u i‖^2))
    (hv : Summable (fun i => ‖v i‖^2)) (x y : E) :
    HasSum (fun i => inner ℂ x (u i)*inner ℂ (v i) y) (inner ℂ x (operator u v y)) := by
  convert! ((hasSum_operator hu hv).mapL (ContinuousLinearMap.apply ℂ E y)).mapL (innerSL ℂ x) using 1
  ext i
  simp [InnerProductSpace.rankOne_apply, mul_comm]

omit [CompleteSpace E] in
theorem square_coordinates_summable (b : HilbertBasis J ℂ E) {u : I → E}
    (hu : Summable (fun i => ‖u i‖^2)) :
    Summable (fun ij : I × J => ‖inner ℂ (b ij.2) (u ij.1)‖^2) := by
  apply (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mpr
  have hh (i : I) : HasSum (fun j => ‖inner ℂ (b j) (u i)‖^2) (‖u i‖^2) := by
    have ht := (b.hasSum_inner_mul_inner (u i) (u i)).mapL Complex.reCLM
    convert! ht using 1
    · ext j
      rw [← inner_conj_symm (u i) (b j), mul_comm, Complex.mul_conj]
      simp only [Complex.reCLM_apply, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
    · simp [← Complex.ofReal_pow]
  refine ⟨fun i => (hh i).summable, ?_⟩
  simpa only [(hh _).tsum_eq] using hu

omit [CompleteSpace E] in
theorem trace_norm_summable (b : HilbertBasis J ℂ E) {u v : I → E}
    (hu : Summable (fun i => ‖u i‖^2)) (hv : Summable (fun i => ‖v i‖^2)) :
    Summable (fun ij : I × J => ‖inner ℂ (b ij.2) (u ij.1)*inner ℂ (v ij.1) (b ij.2)‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    ((square_coordinates_summable b hu).add (square_coordinates_summable b hv))
  intro ij
  rw [norm_mul, norm_inner_symm (v ij.1)]
  nlinarith [sq_nonneg (‖inner ℂ (b ij.2) (u ij.1)‖-‖inner ℂ (b ij.2) (v ij.1)‖)]

def pairing (u v : I → E) (Z : E →L[ℂ] E) : ℂ := ∑' i, inner ℂ (v i) (Z (u i))

omit [CompleteSpace E] in
theorem applied_summable {u : I → E} (hu : Summable (fun i => ‖u i‖^2)) (Z : E →L[ℂ] E) :
    Summable (fun i => ‖Z (u i)‖^2) := by
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _ (hu.mul_left (‖Z‖^2))
  intro i
  calc
    _ ≤ (‖Z‖*‖u i‖)^2 := pow_le_pow_left₀ (norm_nonneg _) (Z.le_opNorm _) _
    _ = _ := mul_pow _ _ _

omit [CompleteSpace E] in
theorem pairing_summable {u v : I → E} (hu : Summable (fun i => ‖u i‖^2))
    (hv : Summable (fun i => ‖v i‖^2)) (Z : E →L[ℂ] E) :
    Summable (fun i => inner ℂ (v i) (Z (u i))) :=
  (norm_product_summable hv (applied_summable hu Z)).of_norm_bounded
    (fun _i => norm_inner_le_norm _ _)

theorem trace_hasSum (b : HilbertBasis J ℂ E) {u v : I → E}
    (hu : Summable (fun i => ‖u i‖^2)) (hv : Summable (fun i => ‖v i‖^2)) :
    HasSum (fun j => inner ℂ (b j) (operator u v (b j)))
      (∑' i, inner ℂ (v i) (u i)) := by
  have hh := (trace_norm_summable b hu hv).of_norm
  have hi (i : I) : HasSum (fun j => inner ℂ (b j) (u i)*inner ℂ (v i) (b j)) (inner ℂ (v i) (u i)) := by
    simpa only [mul_comm] using b.hasSum_inner_mul_inner (v i) (u i)
  have he (j : J) := entry_hasSum hu hv (b j) (b j)
  have hf := hh.hasSum.prod_fiberwise (f := fun ij : I × J => inner ℂ (b ij.2) (u ij.1)*inner ℂ (v ij.1) (b ij.2)) hi
  have hg := hh.prod_symm.hasSum.prod_fiberwise (f := fun ji : J × I => inner ℂ (b ji.1) (u ji.2)*inner ℂ (v ji.2) (b ji.1)) he
  have ht : (∑' j, inner ℂ (b j) (operator u v (b j)))=∑' i, inner ℂ (v i) (u i) := by
    rw [hg.tsum_eq, hf.tsum_eq]
    exact (Equiv.prodComm J I).tsum_eq (fun ij : I × J => inner ℂ (b ij.2) (u ij.1)*inner ℂ (v ij.1) (b ij.2))
  exact ht ▸ hg.summable.hasSum

theorem operator_comp_left {u v : I → E} (hu : Summable (fun i => ‖u i‖^2))
    (hv : Summable (fun i => ‖v i‖^2)) (Z : E →L[ℂ] E) :
    Z ∘L operator u v=operator (fun i => Z (u i)) v := by
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  have hh := ((hasSum_operator hu hv).mapL (ContinuousLinearMap.apply ℂ E y)).mapL Z
  have ht := hh.mapL (innerSL ℂ x)
  have ht' : HasSum (fun i => inner ℂ x (Z (u i))*inner ℂ (v i) y)
      (inner ℂ x (Z (operator u v y))) := by
    convert! ht using 1
    ext i
    simp [InnerProductSpace.rankOne_apply, mul_comm]
  exact ht'.unique (entry_hasSum (applied_summable hu Z) hv x y)

theorem pairing_trace (b : HilbertBasis J ℂ E) {u v : I → E}
    (hu : Summable (fun i => ‖u i‖^2)) (hv : Summable (fun i => ‖v i‖^2)) (Z : E →L[ℂ] E) :
    HasSum (fun j => inner ℂ (b j) (Z (operator u v (b j)))) (pairing u v Z) := by
  have hh := trace_hasSum b (applied_summable hu Z) hv
  rw [← operator_comp_left hu hv Z] at hh
  exact hh

 theorem pairing_eq_of_operator_eq {K : Type*} (b : HilbertBasis J ℂ E)
    {u v : I → E} {x y : K → E}
    (hu : Summable (fun i => ‖u i‖^2)) (hv : Summable (fun i => ‖v i‖^2))
    (hx : Summable (fun i => ‖x i‖^2)) (hy : Summable (fun i => ‖y i‖^2))
    (he : operator u v=operator x y) (Z : E →L[ℂ] E) : pairing u v Z=pairing x y Z := by
  apply HasSum.unique (pairing_trace b hu hv Z)
  rw [he]
  exact pairing_trace b hx hy Z
end CrossEnsemble

namespace CrossEnsemble
open scoped BigOperators ComplexConjugate
variable {I J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem operator_adjoint {u v : I → E} (hu : Summable (fun i => ‖u i‖^2))
    (hv : Summable (fun i => ‖v i‖^2)) : (operator u v).adjoint=operator v u := by
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_right]
  have hh := (entry_hasSum hu hv y x).mapL Complex.conjCLE.toContinuousLinearMap
  change HasSum (fun i => conj (inner ℂ y (u i)*inner ℂ (v i) x))
    (conj (inner ℂ y (operator u v x))) at hh
  simp only [map_mul, inner_conj_symm] at hh
  have hh' : HasSum (fun i => inner ℂ x (v i)*inner ℂ (u i) y)
      (inner ℂ (operator u v x) y) := by
    convert! hh using 1
    ext i
    ring
  exact hh'.unique (entry_hasSum hv hu x y)

theorem operator_sandwich {u v : I → E} (hu : Summable (fun i => ‖u i‖^2))
    (hv : Summable (fun i => ‖v i‖^2)) (Z : E →L[ℂ] E) :
    Z ∘L operator u v ∘L Z.adjoint=operator (fun i => Z (u i)) (fun i => Z (v i)) := by
  have hr : operator u v ∘L Z.adjoint=operator u (fun i => Z (v i)) := by
    have hh := congrArg ContinuousLinearMap.adjoint (operator_comp_left hv hu Z)
    simpa only [ContinuousLinearMap.adjoint_comp, operator_adjoint hv hu,
      operator_adjoint (applied_summable hv Z) hu] using hh
  rw [hr, operator_comp_left hu (applied_summable hv Z) Z]
end CrossEnsemble

namespace Annihilation
open EntropyPhotonNumber QuantumTrace
open scoped BigOperators ComplexConjugate
variable {n : ℕ}

def modeBound (j : Fin n) (upward : Bool) : Fock n →L[ℂ] Fock n :=
  WeightedShift.pullCLM id Function.injective_id
    (fun k => (((k j:ℝ)+(if upward then 1 else 0))/numberWeight k : ℝ)) 1 (by norm_num) (by
    intro k
    have hk := numberWeight_one_le k
    have hc := coordinate_le_weight j k
    have hp : 0 < numberWeight k := by linarith
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    apply (div_le_iff₀ hp).mpr
    cases upward <;> norm_num at * <;> linarith)

@[simp] theorem modeBound_apply (j : Fin n) (upward : Bool) (x : Fock n) (k : NumberIndex n) :
    modeBound j upward x k =
      ((((k j:ℝ)+(if upward then 1 else 0))/numberWeight k : ℝ):ℂ)*x k := rfl

theorem modeBound_selfAdjoint (j : Fin n) (upward : Bool) : IsSelfAdjoint (modeBound j upward) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  apply HasSum.unique (lp.hasSum_inner (𝕜 := ℂ) (modeBound j upward x) y)
  convert! lp.hasSum_inner (𝕜 := ℂ) x (modeBound j upward y) using 1
  ext k
  simp only [modeBound_apply, RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

theorem modeBound_inverse_commute (j : Fin n) (upward : Bool) (m : ℕ) :
    modeBound j upward ∘L inverseWeight m=inverseWeight m ∘L modeBound j upward := by
  ext x k
  simp only [ContinuousLinearMap.comp_apply, modeBound_apply, inverseWeight_apply]
  ring

theorem sandwich_right_inverse (a b t : ℕ) (hab : a+1 ≤ b) (j : Fin n) :
    sandwich a (b+t) (by omega) j = sandwich a b hab j ∘L inverseWeight t := by
  ext x k
  simp only [sandwich_apply, coefficient, inverseWeight_apply, ContinuousLinearMap.comp_apply,
    Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow, pow_add]
  ring

theorem creationSandwich_right_inverse (a b t : ℕ) (hab : a+1 ≤ b) (j : Fin n) :
    creationSandwich a (b+t) (by omega) j = creationSandwich a b hab j ∘L inverseWeight t := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext k
  rcases index_cases j k with hk | ⟨l,rfl⟩
  · simp [creationSandwich_zero _ _ _ _ _ k hk]
  · simp only [creationSandwich_up, creationCoefficient, inverseWeight_apply, ContinuousLinearMap.comp_apply,
      Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow, pow_add]
    ring

def gain (j : Fin n) (upward : Bool) : Fock n →L[ℂ] Fock n :=
  if upward then creationSandwich 2 3 (by omega) j else sandwich 2 3 (by omega) j

def unweightedGain (j : Fin n) (upward : Bool) : Fock n →L[ℂ] Fock n :=
  if upward then raising j else lowering j

theorem gain_factor (j : Fin n) (upward : Bool) :
    inverseWeight 2 ∘L gain j upward=unweightedGain j upward ∘L inverseWeight 2 := by
  cases upward
  · exact (sandwich_factor 2 3 (by omega) j).symm.trans (sandwich_right_inverse 0 1 2 (by omega) j)
  · exact (creationSandwich_factor 2 3 (by omega) j).symm.trans (creationSandwich_right_inverse 0 1 2 (by omega) j)

theorem quadratic_coordinate (w t : ℝ) (hw : 0 < w) (z : ℂ) :
    ((w:ℂ)^2)⁻¹ * ((t:ℂ)/(w:ℂ)*z) * (((w:ℂ)^3)⁻¹*conj z)=
      (t:ℂ)*((((|w|:ℝ):ℂ)^3)⁻¹*(‖z‖:ℂ))^2 := by
  rw [abs_of_pos hw]
  calc
    _ = (t:ℂ)*(w:ℂ)⁻¹^6*(z*conj z) := by ring
    _ = _ := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
      ring

theorem mode_quadratic (j : Fin n) (upward : Bool) (x : Fock n) :
    inner ℂ (inverseWeight 3 x) (inverseWeight 2 (modeBound j upward x))=
      (‖unweightedGain j upward (inverseWeight 2 x)‖^2:ℝ) := by
  have hh : HasSum (fun k : NumberIndex n =>
      ((k j:ℝ)+(if upward then 1 else 0))*‖inverseWeight 3 x k‖^2)
      (‖unweightedGain j upward (inverseWeight 2 x)‖^2) := by
    have hi : inverseWeight 1 (inverseWeight 2 x)=inverseWeight 3 x := by
      exact congrArg (fun T : Fock n →L[ℂ] Fock n => T x) (inverseWeight_add 1 2).symm
    cases upward
    · simpa only [Bool.false_eq_true, ↓reduceIte, add_zero, unweightedGain, hi] using lowering_norm_sum j (inverseWeight 2 x)
    · simpa only [↓reduceIte, unweightedGain, hi] using raising_norm_sum j (inverseWeight 2 x)
  apply HasSum.unique (lp.hasSum_inner (𝕜 := ℂ) (inverseWeight 3 x) (inverseWeight 2 (modeBound j upward x)))
  convert! hh.mapL Complex.ofRealCLM using 1
  ext k
  simp only [RCLike.inner_apply, inverseWeight_apply, modeBound_apply, Complex.ofRealCLM_apply,
    map_mul, map_inv₀, map_pow, Complex.conj_ofReal, norm_mul, norm_inv, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_inv, Complex.ofReal_div]
  exact quadratic_coordinate _ _ (by have := numberWeight_one_le k; linarith) (x k)
end Annihilation

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation
open scoped BigOperators
variable {n : ℕ} {I J : Type*}


def dissipator (x : I → Fock n) (j : Fin n) (upward : Bool) : Fock n →L[ℂ] Fock n :=
  CrossEnsemble.operator (fun i => gain j upward (x i)) (fun i => gain j upward (x i))-
    (2:ℂ)⁻¹ • (CrossEnsemble.operator (fun i => modeBound j upward (x i)) (fun i => inverseWeight 1 (x i))+
      CrossEnsemble.operator (fun i => inverseWeight 1 (x i)) (fun i => modeBound j upward (x i)))

def generator (r : ℝ) (x : I → Fock n) : Fock n →L[ℂ] Fock n :=
  ∑ j, (((r+1:ℝ):ℂ) • dissipator x j false+(r:ℂ) • dissipator x j true)

def pairing (r : ℝ) (x : I → Fock n) (Z : Fock n →L[ℂ] Fock n) : ℂ :=
  ∑ j, (((r+1:ℝ):ℂ)*(CrossEnsemble.pairing (fun i => gain j false (x i)) (fun i => gain j false (x i)) Z-
      (2:ℂ)⁻¹*(CrossEnsemble.pairing (fun i => modeBound j false (x i)) (fun i => inverseWeight 1 (x i)) Z+
        CrossEnsemble.pairing (fun i => inverseWeight 1 (x i)) (fun i => modeBound j false (x i)) Z))+
    (r:ℂ)*(CrossEnsemble.pairing (fun i => gain j true (x i)) (fun i => gain j true (x i)) Z-
      (2:ℂ)⁻¹*(CrossEnsemble.pairing (fun i => modeBound j true (x i)) (fun i => inverseWeight 1 (x i)) Z+
        CrossEnsemble.pairing (fun i => inverseWeight 1 (x i)) (fun i => modeBound j true (x i)) Z)))

theorem pairing_hasSum (b : HilbertBasis J ℂ (Fock n)) (r : ℝ) (x : I → Fock n)
    (hx : Summable (fun i => ‖x i‖^2)) (Z : Fock n →L[ℂ] Fock n) :
    HasSum (fun k => inner ℂ (b k) (Z (generator r x (b k)))) (pairing r x Z) := by
  have ha (j : Fin n) (u : Bool) := CrossEnsemble.applied_summable hx (gain j u)
  have hb (j : Fin n) (u : Bool) := CrossEnsemble.applied_summable hx (modeBound j u)
  have hc := CrossEnsemble.applied_summable hx (inverseWeight 1)
  have h (j : Fin n) (u : Bool) :=
    (CrossEnsemble.pairing_trace b (ha j u) (ha j u) Z).sub
      (((CrossEnsemble.pairing_trace b (hb j u) hc Z).add
        (CrossEnsemble.pairing_trace b hc (hb j u) Z)).mul_left (2:ℂ)⁻¹)
  have hh := hasSum_sum fun j (_hj : j ∈ (Finset.univ : Finset (Fin n))) =>
    ((h j false).mul_left ((r+1:ℝ):ℂ)).add ((h j true).mul_left (r:ℂ))
  convert! hh using 1
  ext k
  simp only [generator, dissipator, sum_apply, add_apply,
    sub_apply, smul_apply, map_sum, map_add, map_sub, map_smul,
    inner_sum, inner_sub_right, inner_add_right, inner_smul_right]

end WeightedGenerator

end

end

end OAI
