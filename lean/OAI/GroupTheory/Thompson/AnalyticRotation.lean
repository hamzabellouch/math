import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace OAI

/-!
# The rank-two rotations in the displacement construction

These are actual bounded operators on a real inner-product space. The formula
has no choice of orthogonal complement and remains valid when the two unit
vectors coincide. The estimates use the operator norm.
-/

noncomputable section

universe uE uX

namespace ThompsonNonamenability.Analytic

open scoped InnerProductSpace NNReal

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The skew rank-two operator associated with an ordered pair. -/
def skew (u v : E) : E →L[ℝ] E :=
  (innerSL ℝ u).smulRight v - (innerSL ℝ v).smulRight u

@[simp] theorem skew_apply (u v x : E) :
    skew u v x = ⟪u, x⟫_ℝ • v - ⟪v, x⟫_ℝ • u := rfl

/-- The rotation taking `u` to `v`, on the non-antipodal unit-pair domain. -/
def rotation (u v : E) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E + skew u v +
    (1 + ⟪u, v⟫_ℝ)⁻¹ • (skew u v).comp (skew u v)

theorem rotation_apply (u v x : E) :
    rotation u v x = x + skew u v x +
      (1 + ⟪u, v⟫_ℝ)⁻¹ • skew u v (skew u v x) := rfl

@[simp] theorem skew_self (u : E) : skew u u = 0 := by
  simp [skew]

@[simp] theorem rotation_self (u : E) :
    rotation u u = ContinuousLinearMap.id ℝ E := by
  simp [rotation]

theorem skew_inner (u v x y : E) :
    ⟪skew u v x, y⟫_ℝ = -⟪x, skew u v y⟫_ℝ := by
  simp only [skew_apply, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm v x, real_inner_comm u x]
  ring

theorem rotation_apply_explicit (u v x : E)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    rotation u v x = x +
      (⟪u, x⟫_ℝ + (1 + ⟪u, v⟫_ℝ)⁻¹ *
        (⟪u, v⟫_ℝ * ⟪u, x⟫_ℝ - ⟪v, x⟫_ℝ)) • v +
      (-⟪v, x⟫_ℝ + (1 + ⟪u, v⟫_ℝ)⁻¹ *
        (⟪u, v⟫_ℝ * ⟪v, x⟫_ℝ - ⟪u, x⟫_ℝ)) • u := by
  have huu : ⟪u, u⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, hu]; norm_num
  have hvv : ⟪v, v⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, hv]; norm_num
  simp only [rotation_apply, skew_apply, inner_sub_right,
    real_inner_smul_right, huu, hvv, real_inner_comm u v]
  module

theorem rotation_apply_self (u v : E)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hκ : 0 ≤ ⟪u, v⟫_ℝ) :
    rotation u v u = v := by
  have huu : ⟪u, u⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, hu]; norm_num
  have hd : 1 + ⟪u, v⟫_ℝ ≠ 0 := by linarith
  rw [rotation_apply_explicit u v u hu hv, huu, real_inner_comm u v]
  match_scalars <;> field_simp [hd] <;> ring

theorem rotation_inner (u v : E)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hκ : 0 ≤ ⟪u, v⟫_ℝ)
    (x y : E) :
    ⟪rotation u v x, rotation u v y⟫_ℝ = ⟪x, y⟫_ℝ := by
  have huu : ⟪u, u⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, hu]; norm_num
  have hvv : ⟪v, v⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, hv]; norm_num
  have hd : 1 + ⟪u, v⟫_ℝ ≠ 0 := by linarith
  rw [rotation_apply_explicit u v x hu hv,
    rotation_apply_explicit u v y hu hv]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, huu, hvv, real_inner_comm u v,
    real_inner_comm u x, real_inner_comm v x]
  field_simp [hd]
  ring

theorem rotation_norm (u v : E)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hκ : 0 ≤ ⟪u, v⟫_ℝ)
    (x : E) : ‖rotation u v x‖ = ‖x‖ := by
  rw [norm_eq_sqrt_real_inner, rotation_inner u v hu hv hκ,
    ← norm_eq_sqrt_real_inner]

theorem norm_rotation_le_one (u v : E)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hκ : 0 ≤ ⟪u, v⟫_ℝ) :
    ‖rotation u v‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [rotation_norm u v hu hv hκ, one_mul]

theorem norm_rotation (u v : E)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hκ : 0 ≤ ⟪u, v⟫_ℝ) :
    ‖rotation u v‖ = 1 := by
  apply le_antisymm (norm_rotation_le_one u v hu hv hκ)
  have h := (rotation u v).le_opNorm u
  rw [rotation_norm u v hu hv hκ, hu, mul_one] at h
  exact h

theorem rotation_inner_swap (u v x y : E) :
    ⟪rotation u v x, y⟫_ℝ = ⟪x, rotation v u y⟫_ℝ := by
  have hs (z : E) : skew v u z = -skew u v z := by
    simp only [skew_apply]
    module
  simp only [rotation_apply, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, skew_inner,
    hs, map_neg, inner_neg_right, neg_neg, real_inner_comm u v]

theorem rotation_reverse_apply (u v : E)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hκ : 0 ≤ ⟪u, v⟫_ℝ)
    (x : E) : rotation v u (rotation u v x) = x := by
  apply ext_inner_right ℝ
  intro y
  rw [rotation_inner_swap, rotation_inner u v hu hv hκ]

theorem rotation_surjective (u v : E)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hκ : 0 ≤ ⟪u, v⟫_ℝ) :
    Function.Surjective (rotation u v) := by
  intro x
  refine ⟨rotation v u x, ?_⟩
  exact rotation_reverse_apply v u hv hu
    (by simpa only [real_inner_comm u v] using hκ) x

def rankOne (u v : E) : E →L[ℝ] E := (innerSL ℝ u).smulRight v

/-- The operator polynomial used in the rank-two rotation formula. -/
def rotationPolynomial (A : E →L[ℝ] E) (c : ℝ) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E + A + c • A.comp A

@[simp] lemma norm_rankOne (u v : E) : ‖rankOne u v‖ = ‖u‖ * ‖v‖ := by
  simp only [rankOne, ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm]

lemma rankOne_sub (u v u' v' : E) :
    rankOne u v - rankOne u' v' =
      rankOne (u - u') v + rankOne u' (v - v') := by
  ext x
  simp only [rankOne, sub_apply, add_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_sub_left,
    sub_smul, smul_sub]
  abel

lemma norm_rankOne_sub_le (u v u' v' : E) :
    ‖rankOne u v - rankOne u' v'‖ ≤
      ‖u - u'‖ * ‖v‖ + ‖u'‖ * ‖v - v'‖ := by
  rw [rankOne_sub]
  simpa only [norm_rankOne] using
    norm_add_le (rankOne (u - u') v) (rankOne u' (v - v'))

lemma norm_skew_le_two (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖skew u v‖ ≤ 2 := by
  calc
    ‖skew u v‖ ≤ ‖rankOne u v‖ + ‖rankOne v u‖ := norm_sub_le _ _
    _ = 2 := by simp only [norm_rankOne, hu, hv]; norm_num

lemma norm_skew_sub_le (u v u' v' : E)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hu' : ‖u'‖ = 1) (hv' : ‖v'‖ = 1) :
    ‖skew u v - skew u' v'‖ ≤ 2 * (‖u - u'‖ + ‖v - v'‖) := by
  have heq : skew u v - skew u' v' =
      (rankOne u v - rankOne u' v') - (rankOne v u - rankOne v' u') := by
    unfold skew rankOne
    abel
  have h₁ := norm_rankOne_sub_le u v u' v'
  have h₂ := norm_rankOne_sub_le v u v' u'
  rw [hv, hu', mul_one, one_mul] at h₁
  rw [hu, hv', mul_one, one_mul] at h₂
  rw [heq]
  calc
    _ ≤ ‖rankOne u v - rankOne u' v'‖ + ‖rankOne v u - rankOne v' u'‖ :=
      norm_sub_le _ _
    _ ≤ (‖u - u'‖ + ‖v - v'‖) + (‖v - v'‖ + ‖u - u'‖) :=
      add_le_add h₁ h₂
    _ = 2 * (‖u - u'‖ + ‖v - v'‖) := by ring

lemma inner_sub_inner_le (u v u' v' : E) (hv : ‖v‖ = 1) (hu' : ‖u'‖ = 1) :
    |⟪u, v⟫_ℝ - ⟪u', v'⟫_ℝ| ≤ ‖u - u'‖ + ‖v - v'‖ := by
  have heq : ⟪u, v⟫_ℝ - ⟪u', v'⟫_ℝ =
      ⟪u - u', v⟫_ℝ + ⟪u', v - v'⟫_ℝ := by
    rw [inner_sub_left, inner_sub_right]
    ring
  calc
    |⟪u, v⟫_ℝ - ⟪u', v'⟫_ℝ| =
        ‖⟪u - u', v⟫_ℝ + ⟪u', v - v'⟫_ℝ‖ := by
      rw [heq, Real.norm_eq_abs]
    _ ≤ ‖⟪u - u', v⟫_ℝ‖ + ‖⟪u', v - v'⟫_ℝ‖ := norm_add_le _ _
    _ ≤ ‖u - u'‖ * ‖v‖ + ‖u'‖ * ‖v - v'‖ :=
      add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ = ‖u - u'‖ + ‖v - v'‖ := by rw [hv, hu', mul_one, one_mul]

lemma inverse_one_add_bounds (κ : ℝ) (hκ : 0 ≤ κ) :
    0 ≤ (1 + κ)⁻¹ ∧ (1 + κ)⁻¹ ≤ 1 := by
  constructor
  · exact inv_nonneg.mpr (by linarith)
  · exact inv_le_one_of_one_le₀ (by linarith)

lemma inverse_one_add_difference (κ κ' d : ℝ)
    (hκ : 0 ≤ κ) (hκ' : 0 ≤ κ') (h : |κ - κ'| ≤ d) :
    |(1 + κ)⁻¹ - (1 + κ')⁻¹| ≤ d := by
  have hp : 0 < 1 + κ := by linarith
  have hp' : 0 < 1 + κ' := by linarith
  have hsub : (1 + κ') - (1 + κ) = κ' - κ := by ring
  calc
    |(1 + κ)⁻¹ - (1 + κ')⁻¹|
        = |κ - κ'| / ((1 + κ) * (1 + κ')) := by
          rw [inv_sub_inv (ne_of_gt hp) (ne_of_gt hp'), abs_div,
            abs_of_pos (mul_pos hp hp'), hsub, abs_sub_comm κ' κ]
    _ ≤ |κ - κ'| :=
      div_le_self (abs_nonneg _) (by nlinarith [mul_nonneg hκ hκ'])
    _ ≤ d := h

-- This lemma is independent of the rank-two construction.
lemma norm_rotationPolynomial_sub_le (A B : E →L[ℝ] E) (c c' d : ℝ)
    (hd : 0 ≤ d) (hA : ‖A‖ ≤ 2) (hB : ‖B‖ ≤ 2)
    (hAB : ‖A - B‖ ≤ 2 * d) (hcc' : |c - c'| ≤ d)
    (hc' : |c'| ≤ 1) :
    ‖rotationPolynomial A c - rotationPolynomial B c'‖ ≤ 14 * d := by
  have hAA : ‖A.comp A‖ ≤ 4 := by
    calc
      ‖A.comp A‖ ≤ ‖A‖ * ‖A‖ := A.opNorm_comp_le A
      _ ≤ 2 * 2 := mul_le_mul hA hA (norm_nonneg _) (by norm_num)
      _ = 4 := by norm_num
  have h2d : 0 ≤ 2 * d := mul_nonneg (by norm_num) hd
  have hsquare : A.comp A - B.comp B = (A - B).comp A + B.comp (A - B) := by
    rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
    abel
  have hsq : ‖A.comp A - B.comp B‖ ≤ 8 * d := by
    rw [hsquare]
    calc
      _ ≤ ‖(A - B).comp A‖ + ‖B.comp (A - B)‖ := norm_add_le _ _
      _ ≤ ‖A - B‖ * ‖A‖ + ‖B‖ * ‖A - B‖ :=
        add_le_add ((A - B).opNorm_comp_le A) (B.opNorm_comp_le (A - B))
      _ ≤ (2 * d) * 2 + 2 * (2 * d) :=
        add_le_add (mul_le_mul hAB hA (norm_nonneg _) h2d)
          (mul_le_mul hB hAB (norm_nonneg _) (by norm_num))
      _ = 8 * d := by ring
  have hcoeff : ‖(c - c') • A.comp A‖ ≤ 4 * d := by
    calc
      ‖(c - c') • A.comp A‖ ≤ |c - c'| * ‖A.comp A‖ := by
        simpa only [Real.norm_eq_abs] using
          ContinuousLinearMap.opNorm_smul_le (c - c') (A.comp A)
      _ ≤ d * 4 := mul_le_mul hcc' hAA (norm_nonneg _) hd
      _ = 4 * d := by ring
  have hquadratic : ‖c' • (A.comp A - B.comp B)‖ ≤ 8 * d := by
    calc
      ‖c' • (A.comp A - B.comp B)‖ ≤ |c'| * ‖A.comp A - B.comp B‖ := by
        simpa only [Real.norm_eq_abs] using
          ContinuousLinearMap.opNorm_smul_le c' (A.comp A - B.comp B)
      _ ≤ 1 * (8 * d) := mul_le_mul hc' hsq (norm_nonneg _) (by norm_num)
      _ = 8 * d := one_mul _
  have hsplit : rotationPolynomial A c - rotationPolynomial B c' =
      (A - B) + ((c - c') • A.comp A + c' • (A.comp A - B.comp B)) := by
    unfold rotationPolynomial
    rw [sub_smul, smul_sub]
    abel
  rw [hsplit]
  calc
    _ ≤ ‖A - B‖ + ‖(c - c') • A.comp A + c' • (A.comp A - B.comp B)‖ :=
      norm_add_le _ _
    _ ≤ ‖A - B‖ + (‖(c - c') • A.comp A‖ + ‖c' • (A.comp A - B.comp B)‖) :=
      add_le_add le_rfl (norm_add_le _ _)
    _ ≤ 2 * d + (4 * d + 8 * d) := add_le_add hAB (add_le_add hcoeff hquadratic)
    _ = 14 * d := by ring

lemma norm_rotation_sub_le (u v u' v' : E)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hu' : ‖u'‖ = 1) (hv' : ‖v'‖ = 1)
    (hκ : 0 ≤ ⟪u, v⟫_ℝ) (hκ' : 0 ≤ ⟪u', v'⟫_ℝ) :
    ‖rotation u v - rotation u' v'‖ ≤ 14 * (‖u - u'‖ + ‖v - v'‖) := by
  have hc' := inverse_one_add_bounds (⟪u', v'⟫_ℝ) hκ'
  apply norm_rotationPolynomial_sub_le
  · exact add_nonneg (norm_nonneg _) (norm_nonneg _)
  · exact norm_skew_le_two u v hu hv
  · exact norm_skew_le_two u' v' hu' hv'
  · exact norm_skew_sub_le u v u' v' hu hv hu' hv'
  · exact inverse_one_add_difference _ _ _ hκ hκ' (inner_sub_inner_le u v u' v' hv hu')
  · rw [abs_of_nonneg hc'.1]
    exact hc'.2

/-- Lipschitz dependence of the actual operators on two unit-vector families. -/
theorem rotation_lipschitzWith {X : Type uX} [PseudoMetricSpace X]
    (u v : X → E) {Ku Kv : ℝ≥0}
    (hu : ∀ x, ‖u x‖ = 1) (hv : ∀ x, ‖v x‖ = 1)
    (hκ : ∀ x, 0 ≤ ⟪u x, v x⟫_ℝ)
    (hLu : LipschitzWith Ku u) (hLv : LipschitzWith Kv v) :
    LipschitzWith (14 * (Ku + Kv)) (fun x => rotation (u x) (v x)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm]
  have hu' : ‖u x - u y‖ ≤ (Ku : ℝ) * dist x y := by
    simpa only [dist_eq_norm] using hLu.dist_le_mul x y
  have hv' : ‖v x - v y‖ ≤ (Kv : ℝ) * dist x y := by
    simpa only [dist_eq_norm] using hLv.dist_le_mul x y
  calc
    ‖rotation (u x) (v x) - rotation (u y) (v y)‖
        ≤ 14 * (‖u x - u y‖ + ‖v x - v y‖) :=
      norm_rotation_sub_le _ _ _ _ (hu x) (hv x) (hu y) (hv y) (hκ x) (hκ y)
    _ ≤ 14 * ((Ku : ℝ) * dist x y + (Kv : ℝ) * dist x y) :=
      mul_le_mul_of_nonneg_left (add_le_add hu' hv') (by norm_num)
    _ = (14 * (Ku + Kv) : ℝ≥0) * dist x y := by
      push_cast
      ring

theorem rotation_lipschitzWith_238 {X : Type uX} [PseudoMetricSpace X]
    (u v : X → E)
    (hu : ∀ x, ‖u x‖ = 1) (hv : ∀ x, ‖v x‖ = 1)
    (hκ : ∀ x, 0 ≤ ⟪u x, v x⟫_ℝ)
    (hLu : LipschitzWith 16 u) (hLv : LipschitzWith 1 v) :
    LipschitzWith 238 (fun x => rotation (u x) (v x)) := by
  convert rotation_lipschitzWith u v hu hv hκ hLu hLv using 1 ; norm_num

end ThompsonNonamenability.Analytic

end

end OAI
