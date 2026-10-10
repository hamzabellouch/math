import OAI.Analysis.KadisonKastler.FiniteInnerAveraging
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

namespace OAI

/-! # Order bounds for concrete finite inner averages -/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

namespace FiniteInnerAverage

/-- The ambient average is complex linear. -/
def linear (A : FiniteInnerAverage M) : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H) where
  toFun := A.apply
  map_add' x y := by
    simp only [apply, finiteUnitaryAverage, finiteAverage, unitaryConj,
      mul_add, add_mul, Finset.sum_add_distrib, smul_add]
  map_smul' c x := by
    simp only [apply, finiteUnitaryAverage, finiteAverage, unitaryConj,
      mul_smul_comm, smul_mul_assoc]
    rw [← Finset.smul_sum]
    exact smul_comm _ _ _

@[simp] theorem apply_zero (A : FiniteInnerAverage M) : A.apply 0 = 0 :=
  A.linear.map_zero

/-- The same finite average, with its value retained inside the algebra. -/
def algebraApply (A : FiniteInnerAverage M) (x : Algebra M) : Algebra M :=
  finiteAverage (fun i => (A.unitary i : Algebra M) * x * star (A.unitary i : Algebra M))

theorem algebraApply_val (A : FiniteInnerAverage M) (x : Algebra M) :
    (A.algebraApply x).val = A.apply x.val := by
  let L : Algebra M →ₗ[ℂ] (H →L[ℂ] H) := M.toStarSubalgebra.subtype.toAlgHom.toLinearMap
  change L ((Fintype.card A.Index : ℂ)⁻¹ • ∑ i,
      (A.unitary i : Algebra M) * x * star (A.unitary i : Algebra M)) =
    (Fintype.card A.Index : ℂ)⁻¹ • ∑ i,
      unitaryConj (ambientAlgebraUnitary (A.unitary i)) x.val
  rw [L.map_smul, map_sum]
  rfl

@[simp] theorem algebraApply_sub (A : FiniteInnerAverage M) (x y : Algebra M) :
    A.algebraApply (x - y) = A.algebraApply x - A.algebraApply y := by
  simp only [algebraApply, finiteAverage, mul_sub, sub_mul, Finset.sum_sub_distrib, smul_sub]

/-- Positivity is preserved because every summand is an inner conjugate. -/
theorem apply_nonneg (A : FiniteInnerAverage M) {x : H →L[ℂ] H} (hx : 0 ≤ x) :
    0 ≤ A.apply x := by
  have hs : 0 ≤ ∑ i : A.Index, unitaryConj (ambientAlgebraUnitary (A.unitary i)) x :=
    Finset.sum_nonneg (fun i _ => star_right_conjugate_nonneg hx _)
  have he : (Fintype.card A.Index : ℂ)⁻¹ = (((Fintype.card A.Index : ℝ)⁻¹ : ℝ) : ℂ) := by simp
  have h : 0 ≤ ((Fintype.card A.Index : ℝ)⁻¹) •
      (∑ i : A.Index, unitaryConj (ambientAlgebraUnitary (A.unitary i)) x) :=
    smul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) hs
  have hr := RCLike.real_smul_eq_coe_smul (K := ℂ)
    ((Fintype.card A.Index : ℝ)⁻¹)
    (∑ i : A.Index, unitaryConj (ambientAlgebraUnitary (A.unitary i)) x)
  rw [hr] at h
  change 0 ≤ (Fintype.card A.Index : ℂ)⁻¹ •
    (∑ i : A.Index, unitaryConj (ambientAlgebraUnitary (A.unitary i)) x)
  rw [he]
  exact h

theorem apply_mono (A : FiniteInnerAverage M) {x y : H →L[ℂ] H} (hxy : x ≤ y) :
    A.apply x ≤ A.apply y := by
  have h := A.apply_nonneg (sub_nonneg.mpr hxy)
  rw [apply_sub] at h
  exact sub_nonneg.mp h

/-- A scalar order interval gives a quantitative norm estimate after averaging. -/
theorem norm_apply_sub_scalar_le (A : FiniteInnerAverage M)
    (p q r : H →L[ℂ] H) (α β : ℝ) (hαβ : α ≤ β)
    (hqp : q ≤ p) (hpr : p ≤ r)
    (hq : A.apply q = algebraMap ℝ (H →L[ℂ] H) α)
    (hr : A.apply r = algebraMap ℝ (H →L[ℂ] H) β) :
    ‖A.apply p - algebraMap ℝ (H →L[ℂ] H) α‖ ≤ β - α := by
  have hlo := A.apply_mono hqp
  have hhi := A.apply_mono hpr
  rw [hq] at hlo
  rw [hr] at hhi
  apply (CStarAlgebra.norm_le_iff_le_algebraMap _ (sub_nonneg.mpr hαβ)
    (ha := by exact sub_nonneg.mpr hlo)).mpr
  rw [map_sub]
  exact sub_le_sub_right hhi _

/-- A positive operator supported below a projection whose average is scalar
inherits that scalar norm bound. -/
theorem norm_apply_le_of_positive_interval (A : FiniteInnerAverage M)
    (p r : H →L[ℂ] H) (β : ℝ) (hβ : 0 ≤ β) (hp : 0 ≤ p) (hpr : p ≤ r)
    (hr : A.apply r = algebraMap ℝ (H →L[ℂ] H) β) : ‖A.apply p‖ ≤ β := by
  have h := A.norm_apply_sub_scalar_le p 0 r 0 β hβ hp hpr
    (by rw [apply_zero, map_zero]) hr
  simpa only [map_zero, sub_zero] using h

end FiniteInnerAverage

end

end KadisonKastler

end OAI
