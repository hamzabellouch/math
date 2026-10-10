import OAI.Geometry.SurfaceImmersion.Correction.PeriodicPolynomialExpansion
import OAI.Geometry.SurfaceImmersion.Primitive.PeriodicFiniteAnsatz
import OAI.Geometry.SurfaceImmersion.Geometry.FiniteSeriesAlgebra

namespace OAI

/-! Identifying the finite metric polynomial with derivatives of the actual map. -/

noncomputable section
open scoped BigOperators ContDiff

namespace ClosedSurfaceR4.PeriodicExpansion

open CovarianceCorrector

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

namespace Geometry

variable {dy : A} (g : Geometry (E := E) dy)

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma xTangent_value (dx : A) (U : ℕ → Family A E) (n : ℕ) (p : A) (t : Period) (z : ℝ) :
    vectorPolynomialValue (n + 1) (fun i => (g.xTangent dx U (n + 1) i).val p t) z =
      g.longitudinal.val p t +
        (∑ i ∈ Finset.Ico 1 (n + 1), z ^ i • (xCoefficient dx U i).val p t) +
          z ^ (n + 1) • ((U n).slow dx).val p t := by
  rw [vectorPolynomialValue, weighted_sum_split_endpoints, g.xTangent_zero]
  have he : (∑ i ∈ Finset.Ico 1 (n + 1), z ^ i • (g.xTangent dx U (n + 1) i).val p t) =
      ∑ i ∈ Finset.Ico 1 (n + 1), z ^ i • (xCoefficient dx U i).val p t := by
    apply Finset.sum_congr rfl
    intro i hi
    obtain ⟨hi, hil⟩ := Finset.mem_Ico.mp hi
    rw [g.xTangent_interior dx U (by omega) hil]
  rw [he]
  simp only [xTangent, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false,
    ite_true, Nat.add_sub_cancel]

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma yTangent_value (U : ℕ → Family A E) (L : ℕ) (p : A) (t : Period) (z : ℝ) :
    vectorPolynomialValue L (fun i => (g.yTangent U i).val p t) z =
      g.transverse.val p t + ∑ i ∈ Finset.range L, z ^ (i + 1) • ((U i).slow dy).val p t := by
  rw [vectorPolynomialValue, weighted_sum_split_zero, g.yTangent_zero]
  congr 1
  have he := Finset.sum_Ico_add' (fun i => z ^ i • (g.yTangent U i).val p t) 0 L 1
  simp only [zero_add, Nat.Ico_zero_eq_range] at he
  rw [← he]
  apply Finset.sum_congr rfl
  intro i hi
  rw [g.yTangent_pos U (by omega)]
  simp only [yCoefficient, Nat.add_sub_cancel]

omit [FiniteDimensional ℝ E] in
lemma finiteAnsatz_x {F : A → E} (hF : ContDiff ℝ ∞ F)
    (U : ℕ → Family A E) (hinit : U 0 = g.initial)
    (ℓ : A →L[ℝ] ℝ) (dx : A) (hℓ : ℓ dx = 1)
    (hX : ∀ p, fderiv ℝ F p dx = g.X₀ p + average (g.V.val p))
    (n : ℕ) (z : ℝ) (hz : z ≠ 0) (p : A) :
    fderiv ℝ (finiteAnsatz F U ℓ (n + 1) z) p dx =
      vectorPolynomialValue (n + 1)
        (fun i => (g.xTangent dx U (n + 1) i).val p ((ℓ p / z : ℝ) : Period)) z := by
  let t : Period := ((ℓ p / z : ℝ) : Period)
  have hs : (∑ i ∈ Finset.range (n + 1), z ^ (i + 1) •
      (((U i).slow dx).val p t + (ℓ dx / z) • (U i).angle.val p t)) =
      ∑ i ∈ Finset.range (n + 1),
        (z ^ (i + 1) • ((U i).slow dx).val p t + z ^ i • (U i).angle.val p t) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [smul_add, smul_smul, hℓ]
    congr 1
    congr 1
    field_simp
    ring
  rw [finiteAnsatz_fderiv hF, hs,
    shifted_derivative_sum z (fun i => ((U i).slow dx).val p t)
      (fun i => (U i).angle.val p t) n, g.xTangent_value]
  have hlead : fderiv ℝ F p dx + (U 0).angle.val p t = g.longitudinal.val p t := by
    rw [hinit, g.initial_angle, hX]
    simp only [Family.sub_apply, Family.vectorMean_apply, longitudinal,
      Family.add_apply, Family.constant_apply]
    abel
  simp only [← add_assoc, hlead]
  rfl

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma finiteAnsatz_y {F : A → E} (hF : ContDiff ℝ ∞ F)
    (U : ℕ → Family A E) (ℓ : A →L[ℝ] ℝ) (hℓ : ℓ dy = 0)
    (hY : ∀ p, fderiv ℝ F p dy = g.Y p) (L : ℕ) (z : ℝ) (p : A) :
    fderiv ℝ (finiteAnsatz F U ℓ L z) p dy =
      vectorPolynomialValue L
        (fun i => (g.yTangent U i).val p ((ℓ p / z : ℝ) : Period)) z := by
  rw [finiteAnsatz_fderiv hF, g.yTangent_value, hY]
  simp only [hℓ, zero_div, zero_smul, add_zero, transverse, Family.constant_apply]

end Geometry
end ClosedSurfaceR4.PeriodicExpansion

end

end OAI
