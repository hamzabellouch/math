import OAI.GroupTheory.PolycyclicRecognition.Geometry.PolynomialDerivativeGrowth
import OAI.GroupTheory.PolycyclicRecognition.Geometry.PolynomialMinorDifferential

namespace OAI

/-! # Growing-cube bounds for the actual derivative minors -/

noncomputable section
namespace PolycyclicRecognition

open Set Metric MvPolynomial

theorem norm_finAppend_le {n k : ℕ} {v : Fin n → ℝ} {z : Fin k → ℝ} {R : ℝ}
    (hR : 0 ≤ R) (hv : ‖v‖ ≤ R) (hz : ‖z‖ ≤ R) : ‖Fin.append v z‖ ≤ R := by
  apply (pi_norm_le_iff_of_nonneg hR).mpr
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simpa only [Fin.append_left] using (norm_le_pi_norm v j).trans hv
  · intro j
    simpa only [Fin.append_right] using (norm_le_pi_norm z j).trans hz

theorem norm_appendParameterLinear_le (n k : ℕ) : ‖appendParameterLinear n k‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  rw [one_mul, appendParameterLinear_apply]
  exact norm_finAppend_le (norm_nonneg _) le_rfl (by simp)

theorem dist_finAppend_same {n k : ℕ} (v w : Fin n → ℝ) (z : Fin k → ℝ) :
    dist (Fin.append v z) (Fin.append w z) = dist v w := by
  have h := (Fin.appendIsometry (α := ℝ) n k).isometry.dist_eq (v, z) (w, z)
  change dist (Fin.append v z) (Fin.append w z) = dist (v, z) (w, z) at h
  simpa only [Prod.dist_eq, dist_self, max_eq_left dist_nonneg] using h

theorem uniform_polynomial_slice_derivative_bounds
    {P : Type*} [TopologicalSpace P] {n k : ℕ}
    (p : P → Fin n → MvPolynomial (Fin (n + k)) ℝ) (D : ℕ)
    (hD : ∀ a i, (p a i).totalDegree ≤ D)
    (heval : ∀ i x, Continuous (fun a => eval x (p a i)))
    (S : Set P) (hS : IsCompact S) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ a ∈ S, ∀ R : ℝ, 0 ≤ R →
      (∀ v z, ‖v‖ ≤ R → ‖z‖ ≤ R →
        ‖polynomialSliceDifferential (p a) v z‖ ≤ C * (1 + R) ^ ((n + k) * D)) ∧
      ∀ v w z, ‖v‖ ≤ R → ‖w‖ ≤ R → ‖z‖ ≤ R →
        ‖polynomialSliceDifferential (p a) v z - polynomialSliceDifferential (p a) w z‖ ≤
          C * (1 + R) ^ ((n + k) * D) * dist v w := by
  obtain ⟨C, hC, hbound⟩ := uniform_polynomial_map_derivative_bounds p D hD heval S hS
  refine ⟨C, hC, ?_⟩
  intro a ha R hR
  obtain ⟨hb, hl⟩ := hbound a ha R hR
  have hnorm (A : (Fin (n + k) → ℝ) →L[ℝ] (Fin n → ℝ)) :
      ‖A.comp (appendParameterLinear n k)‖ ≤ ‖A‖ := by
    calc
      _ ≤ ‖A‖ * ‖appendParameterLinear n k‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖A‖ * 1 := mul_le_mul_of_nonneg_left (norm_appendParameterLinear_le n k) (norm_nonneg _)
      _ = ‖A‖ := mul_one _
  constructor
  · intro v z hv hz
    exact (hnorm _).trans (hb _ (norm_finAppend_le hR hv hz))
  · intro v w z hv hw hz
    have he : polynomialSliceDifferential (p a) v z - polynomialSliceDifferential (p a) w z =
        (polynomialMapDifferential (p a) (Fin.append v z) -
          polynomialMapDifferential (p a) (Fin.append w z)).comp (appendParameterLinear n k) := by
      ext x i
      rfl
    rw [he]
    exact (hnorm _).trans (by simpa only [dist_finAppend_same] using
      (hl _ _ (norm_finAppend_le hR hv hz) (norm_finAppend_le hR hw hz)))

end PolycyclicRecognition

end

end OAI
