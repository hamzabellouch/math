import OAI.Geometry.RCD.Harmonic.NearbyMeanGrams
import OAI.Geometry.RCD.Harmonic.TransformedColumns

namespace OAI

/-!
# Relative comparison from exact harmonic normalization

Restricting a normalized splitting map to a subball costs only its volume
ratio. The comparison is relative to the original mean Gram, even if that
Gram has arbitrarily small eigenvalues.
-/

open Set Metric MeasureTheory
open scoped InnerProductSpace ENNReal

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- Exact mean normalization identifies the inverse-coordinate norm
with the original mean energy, even for a very anisotropic Gram. -/
theorem exact_mean_inverse_norm_sq {n : ℕ}
    (U : Euclidean n →L[ℝ] SobolevSpace μ hQ)
    (s : Set X) (hs : MeasurableSet s) (A : Euclidean n ≃L[ℝ] Euclidean n)
    (hA : IsExactMeanNormalization μ hQ U s hs A) (v : Euclidean n) :
    ‖A.symm v‖ ^ 2 = ⟪v, sobolevMeanGram μ hQ U s hs v⟫_ℝ := by
  have hh : ⟪A.symm v, sobolevMeanGram μ hQ
      (U.comp (A : Euclidean n →L[ℝ] Euclidean n)) s hs (A.symm v)⟫_ℝ =
      ‖A.symm v‖ ^ 2 := by
    rw [hA]
    simp only [ContinuousLinearMap.id_apply, real_inner_self_eq_norm_sq]
  rw [sobolevMeanGram_comp] at hh
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] using hh.symm

/-- Exact normalization on the large ball improves the two-mean comparison:
only the restricted mean incurs an error. -/
theorem exact_normalization_subball_bounds {n : ℕ}
    (u : Fin n → SobolevSpace μ hQ) (A : Euclidean n ≃L[ℝ] Euclidean n)
    {p : X} {r ε C : ℝ} {w : X → Euclidean n}
    (hfirst : FirstOrderSplittingOn μ hQ p r ε (transformedColumn μ hQ u A) w)
    (hexact : IsExactMeanNormalization μ hQ (sobolevColumnMap μ hQ u)
      (ball p r) measurableSet_ball A)
    (s : Set X) (hs : MeasurableSet s) (hsub : s ⊆ ball p r)
    (hszero : μ s ≠ 0) (hsfin : μ s ≠ ∞)
    (hrzero : μ (ball p r) ≠ 0) (hrfin : μ (ball p r) ≠ ∞)
    (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hvol : μ.real (ball p r) ≤ C * μ.real s) (v : Euclidean n) :
    (1 - (n : ℝ) ^ 2 * (C * ε)) *
        ⟪v, sobolevMeanGram μ hQ (sobolevColumnMap μ hQ u) (ball p r) measurableSet_ball v⟫_ℝ ≤
      ⟪v, sobolevMeanGram μ hQ (sobolevColumnMap μ hQ u) s hs v⟫_ℝ ∧
    ⟪v, sobolevMeanGram μ hQ (sobolevColumnMap μ hQ u) s hs v⟫_ℝ ≤
      (1 + (n : ℝ) ^ 2 * (C * ε)) *
        ⟪v, sobolevMeanGram μ hQ (sobolevColumnMap μ hQ u) (ball p r) measurableSet_ball v⟫_ℝ := by
  let U := sobolevColumnMap μ hQ u
  have hnorm := meanGram_sub_id_norm_le_of_subset μ hQ (transformedColumn μ hQ u A)
    hs hsub hszero hsfin hrzero hrfin hC hε hvol hfirst.gram
  rw [sobolevColumnMap_transformed] at hnorm
  have hform (b : Set X) (hb : MeasurableSet b) :
      ⟪A.symm v, sobolevMeanGram μ hQ (U.comp (A : Euclidean n →L[ℝ] Euclidean n)) b hb (A.symm v)⟫_ℝ =
        ⟪v, sobolevMeanGram μ hQ U b hb v⟫_ℝ := by
    rw [sobolevMeanGram_comp]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
  have hv : ‖A.symm v‖ ^ 2 =
      ⟪v, sobolevMeanGram μ hQ U (ball p r) measurableSet_ball v⟫_ℝ := by
    exact exact_mean_inverse_norm_sq μ hQ U (ball p r) measurableSet_ball A hexact v
  have hlo := inner_lower_of_sub_id_norm _ hnorm (A.symm v)
  have hup := inner_upper_of_sub_id_norm _ hnorm (A.symm v)
  rw [hform s hs, hv] at hlo hup
  exact ⟨hlo, hup⟩

end RegularPointCoordinates

end

end OAI
