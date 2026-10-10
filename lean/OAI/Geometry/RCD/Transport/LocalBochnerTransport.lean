import OAI.Geometry.RCD.Coordinates.ExactNormalizationComparison
import OAI.Geometry.RCD.Sobolev.LocalBochnerInput
import OAI.Geometry.RCD.Harmonic.TransformedColumns
import OAI.Geometry.RCD.Coordinates.NormalizedBochnerMass

namespace OAI

/-!
# Transport of the canonical Bochner family

One positive bilinear measure supplies every local coordinate normalization.
Restriction and linear coordinate changes preserve this measure and its
singular part through the corresponding pullbacks.
-/

open Set Metric MeasureTheory
open scoped NNReal InnerProductSpace

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {U : E →L[ℝ] SobolevSpace μ hQ} {M : PositiveBilinearMeasure X E}
  {κ : ℝ} {p : X} {r : ℝ} {L : ℝ≥0} {v : E}

/-- Restriction keeps the same energy representative and the same measure. -/
def LocalHarmonicEnergy.restrict
    (G : LocalHarmonicEnergy μ hQ U M κ p r L v)
    {q : X} {s : ℝ} (hsub : ball q (2 * s) ⊆ ball p (2 * r)) :
    LocalHarmonicEnergy μ hQ U M κ q s L v where
  energy := G.energy
  representative := ae_restrict_of_ae_restrict_of_subset hsub G.representative
  bounded := G.bounded
  measure_laplacian φ w hw hws hwsub hwφ :=
    G.measure_laplacian φ w hw hws (hwsub.trans hsub) hwφ

/-- Linear coordinate changes pull back the full positive measure, including
its singular part. The global extension bound pays only the operator norm. -/
def LocalHarmonicEnergy.comp (A : E →L[ℝ] E)
    (G : LocalHarmonicEnergy μ hQ U M κ p r L (A v)) :
    LocalHarmonicEnergy μ hQ (U.comp A) (M.comap A.toLinearMap) κ p r (L * ‖A‖₊) v where
  energy := G.energy
  representative := G.representative
  bounded := by
    filter_upwards [G.bounded] with x hx
    apply hx.trans
    simp only [NNReal.coe_mul, NNReal.coe_pow, coe_nnnorm]
    calc
      (L : ℝ) ^ 2 * ‖A v‖ ^ 2 ≤ (L : ℝ) ^ 2 * (‖A‖ * ‖v‖) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (A.le_opNorm v) 2) (sq_nonneg _)
      _ = _ := by ring
  measure_laplacian := G.measure_laplacian

/-- A normalized splitting error controls the original Bochner measure
in the transformed direction. All scales use the same original measure. -/
theorem transformed_harmonic_mass_le [IsFiniteMeasureOnCompacts μ]
    {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (M : PositiveBilinearMeasure X (Euclidean n))
    {p : X} {r ρ C κ : ℝ} {L : ℝ≥0}
    (G : ∀ v, LocalHarmonicEnergy μ hQ (sobolevColumnMap μ hQ u) M κ p r L v)
    (A : Euclidean n ≃L[ℝ] Euclidean n)
    (χ : GoodLaplacianCutoff μ hQ p ρ C)
    (hρ : 0 < ρ) (hρr : ρ < r) (hC : 0 ≤ C) (hκ : 0 ≤ κ)
    {ε : ℝ} (hε : 0 ≤ ε)
    (herror : ∀ i j : Fin n, ∫ x in closedBall p (2 * ρ),
      |localGamma μ hQ (transformedColumn μ hQ u A i)
        (transformedColumn μ hQ u A j) x - (if i = j then 1 else 0)| ∂μ ≤ ε)
    (v : Euclidean n) :
    ⟪A v, M.massOperator (ball p ρ) (A v)⟫_ℝ ≤
      ((C / ρ ^ 2) * ((n : ℝ) ^ 2 * ε) / 2 +
        κ * ((n : ℝ) ^ 2 * ε + μ.real (closedBall p (2 * ρ)))) * ‖v‖ ^ 2 := by
  have hG (v : Euclidean n) : LocalHarmonicEnergy μ hQ
      (sobolevColumnMap μ hQ (transformedColumn μ hQ u A))
      (M.comap A.toLinearMap) κ p r (L * ‖(A : Euclidean n →L[ℝ] Euclidean n)‖₊) v := by
    rw [sobolevColumnMap_transformed]
    exact (G (A v)).comp μ hQ (A : Euclidean n →L[ℝ] Euclidean n)
  have h := χ.harmonic_mass_le μ hQ hρ hρr hC hκ (transformedColumn μ hQ u A)
    (M.comap A.toLinearMap) hG hε herror v
  have he : (M.comap A.toLinearMap).massOperator (ball p ρ) =
      (A : Euclidean n →L[ℝ] Euclidean n).adjoint.comp
        ((M.massOperator (ball p ρ)).comp (A : Euclidean n →L[ℝ] Euclidean n)) :=
    M.comap_massOperator (A : Euclidean n →L[ℝ] Euclidean n) (ball p ρ)
  rw [he] at h
  simpa only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right, ContinuousLinearEquiv.coe_coe] using h

/-- The dimensionless splitting estimate applies to the same original
measure in every transformed direction. -/
theorem transformed_normalized_bochner_mass_le [IsFiniteMeasureOnCompacts μ]
    {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (M : PositiveBilinearMeasure X (Euclidean n))
    {p : X} {r ε C κ : ℝ} {L : ℝ≥0}
    (G : ∀ v, LocalHarmonicEnergy μ hQ (sobolevColumnMap μ hQ u) M κ p r L v)
    (A : Euclidean n ≃L[ℝ] Euclidean n) {w : X → Euclidean n}
    (h : FirstOrderSplittingOn μ hQ p (8 * r) ε (transformedColumn μ hQ u A) w)
    (hr : 0 < r) (hε : 0 ≤ ε) (hC : 0 ≤ C) (hκ : 0 ≤ κ)
    (hvol : 0 < μ.real (ball p (8 * r)))
    (χ : GoodLaplacianCutoff μ hQ p (r / 2) C) (v : Euclidean n) :
    (r ^ 2 / μ.real (ball p (8 * r))) * ⟪A v, M.massOperator (ball p (r / 2)) (A v)⟫_ℝ ≤
      (2 * C * (n : ℝ) ^ 2 * ε + κ * r ^ 2 * ((n : ℝ) ^ 2 * ε + 1)) * ‖v‖ ^ 2 := by
  have hG (v : Euclidean n) : LocalHarmonicEnergy μ hQ
      (sobolevColumnMap μ hQ (transformedColumn μ hQ u A))
      (M.comap A.toLinearMap) κ p r (L * ‖(A : Euclidean n →L[ℝ] Euclidean n)‖₊) v := by
    rw [sobolevColumnMap_transformed]
    exact (G (A v)).comp μ hQ (A : Euclidean n →L[ℝ] Euclidean n)
  have hb := splitting_normalized_bochner_mass_le μ hQ h hr hε hC hκ hvol χ
    (M.comap A.toLinearMap) hG v
  have he : (M.comap A.toLinearMap).massOperator (ball p (r / 2)) =
      (A : Euclidean n →L[ℝ] Euclidean n).adjoint.comp
        ((M.massOperator (ball p (r / 2))).comp (A : Euclidean n →L[ℝ] Euclidean n)) :=
    M.comap_massOperator (A : Euclidean n →L[ℝ] Euclidean n) (ball p (r / 2))
  rw [he] at hb
  simpa only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right, ContinuousLinearEquiv.coe_coe] using hb

/-- Returning from exact normalized directions gives a relative mass
bound in the original mean Gram. -/
theorem original_gram_bochner_mass_le [IsFiniteMeasureOnCompacts μ]
    {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (M : PositiveBilinearMeasure X (Euclidean n))
    {p : X} {r ε C κ : ℝ} {L : ℝ≥0}
    (G : ∀ v, LocalHarmonicEnergy μ hQ (sobolevColumnMap μ hQ u) M κ p r L v)
    (A : Euclidean n ≃L[ℝ] Euclidean n) {w : X → Euclidean n}
    (h : FirstOrderSplittingOn μ hQ p (8 * r) ε (transformedColumn μ hQ u A) w)
    (hexact : IsExactMeanNormalization μ hQ (sobolevColumnMap μ hQ u)
      (ball p (8 * r)) measurableSet_ball A)
    (hr : 0 < r) (hε : 0 ≤ ε) (hC : 0 ≤ C) (hκ : 0 ≤ κ)
    (hvol : 0 < μ.real (ball p (8 * r)))
    (χ : GoodLaplacianCutoff μ hQ p (r / 2) C) (v : Euclidean n) :
    (r ^ 2 / μ.real (ball p (8 * r))) * ⟪v, M.massOperator (ball p (r / 2)) v⟫_ℝ ≤
      (2 * C * (n : ℝ) ^ 2 * ε + κ * r ^ 2 * ((n : ℝ) ^ 2 * ε + 1)) *
        ⟪v, sobolevMeanGram μ hQ (sobolevColumnMap μ hQ u) (ball p (8 * r)) measurableSet_ball v⟫_ℝ := by
  have hb := transformed_normalized_bochner_mass_le μ hQ u M G A h hr hε hC hκ hvol χ (A.symm v)
  simpa only [ContinuousLinearEquiv.apply_symm_apply,
    exact_mean_inverse_norm_sq μ hQ (sobolevColumnMap μ hQ u) (ball p (8 * r)) measurableSet_ball A hexact v] using hb

end RegularPointCoordinates

end

end OAI
