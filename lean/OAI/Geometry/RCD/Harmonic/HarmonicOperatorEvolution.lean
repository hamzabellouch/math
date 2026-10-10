import OAI.Geometry.RCD.Coordinates.UniformPolarizedError
import OAI.Geometry.RCD.Heat.HarmonicBochnerHeatSource

namespace OAI

/-! # The full operator-valued harmonic heat equation -/

open Set Metric MeasureTheory
open scoped NNReal InnerProductSpace

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
  {k : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ hQ k)
  {n : ℕ} {U : Euclidean n →L[ℝ] SobolevSpace μ hQ}
  {M : PositiveBilinearMeasure X (Euclidean n)} {κ : ℝ} {p : X} {r : ℝ} {L : ℝ≥0}
  (G : ∀ v, LocalHarmonicEnergy μ hQ U M κ p r L v)
  {ρ C : ℝ} (χ : GoodLaplacianCutoff μ hQ p ρ C)

/-- Polarizing the actual scalar Bochner identities yields the full
operator derivative, with the singular mass measure retained. -/
theorem harmonicHeatGram_hasDerivAt (hρ : 0 < ρ) (hρr : ρ < r)
    {t : ℝ} (ht : 0 < t) (x : X) {lambda : ℝ} (hlambda : 0 ≤ lambda) :
    HasDerivAt
      (fun s => cutoffHeatGramAt μ hQ hk χ.weight.continuous
        (χ.hasCompactSupport μ hQ) U s x lambda)
      ((2 : ℝ) • cutoffHeatMass μ hQ hk χ.weight.continuous
          (χ.hasCompactSupport μ hQ) M ht x -
        (2 * κ) • cutoffHeatGram μ hQ hk χ.weight.continuous
          (χ.hasCompactSupport μ hQ) U ht x 0 +
        harmonicHeatError μ hQ (k := k) G χ t x +
        lambda • ContinuousLinearMap.id ℝ (Euclidean n)) t := by
  let Q := fun s => cutoffHeatGramAt μ hQ hk χ.weight.continuous
    (χ.hasCompactSupport μ hQ) U s x lambda
  let B := cutoffHeatMass μ hQ hk χ.weight.continuous
    (χ.hasCompactSupport μ hQ) M ht x
  let A := cutoffHeatGram μ hQ hk χ.weight.continuous
    (χ.hasCompactSupport μ hQ) U ht x 0
  let e := fun v => ∫ z, k t x z *
    cutoffSourceDensity μ hQ (G v).energy χ.sobolev χ.laplacian z ∂μ
  have hQs (s : ℝ) : (Q s).IsSymmetric := by
    by_cases hs : 0 < s
    · rw [show Q s = cutoffHeatGram μ hQ hk χ.weight.continuous
        (χ.hasCompactSupport μ hQ) U hs x lambda from
        cutoffHeatGramAt_of_pos μ hQ hk _ _ U hs x lambda]
      exact (cutoffHeatGram_isPositive μ hQ hk _ _ U (fun z => (χ.bounds z).1) hs x hlambda).isSymmetric
    · simp only [Q, cutoffHeatGramAt, dite_eq_right hs]
      exact ContinuousLinearMap.isPositive_zero.isSymmetric
  have hB : B.IsSymmetric :=
    (cutoffHeatMass_isPositive μ hQ hk _ _ M (fun z => (χ.bounds z).1) ht x).isSymmetric
  have hA : A.IsSymmetric :=
    (cutoffHeatGram_isPositive μ hQ hk _ _ U (fun z => (χ.bounds z).1) ht x le_rfl).isSymmetric
  have hχΩ : tsupport (χ.weight : X → ℝ) ⊆ ball p (2 * r) := by
    intro z hz
    have hd : dist z p ≤ 2 * ρ := χ.tsupport_subset μ hQ hz
    exact lt_of_le_of_lt hd (by linarith)
  have hχR : ∀ z ∉ closedBall p (2 * ρ), χ.weight z = 0 := by
    intro z hz
    apply χ.zero z
    simpa only [mem_closedBall, dist_comm, not_le] using hz
  have hqR : ∀ᵐ z ∂μ, z ∉ closedBall p (2 * ρ) → χ.laplacian z = 0 := by
    filter_upwards [χ.laplacian_locality] with z hz hn
    apply hz (Or.inr _)
    simpa only [mem_closedBall, dist_comm, not_le] using hn
  have hd (v : Euclidean n) : HasDerivAt (fun s => ⟪v, Q s v⟫_ℝ)
      (2 * ⟪v, B v⟫_ℝ - 2 * κ * ⟪v, A v⟫_ℝ + e v + lambda * ‖v‖ ^ 2) t :=
    (G v).heatGram_hasDerivAt_mass μ hQ hk χ.weight (χ.hasCompactSupport μ hQ)
      hχΩ χ.sobolev χ.representative χ.laplacian χ.weak_laplacian p
      (mul_pos (by norm_num) hρ) hχR hqR ht x lambda
  have h := hasDerivAt_operator_of_quadratic hQs _ hd
  have hid := polarizedDerivative_quadratic_form
    (ContinuousLinearMap.id ℝ (Euclidean n)) ContinuousLinearMap.isPositive_id.isSymmetric
  simp only [ContinuousLinearMap.id_apply, real_inner_self_eq_norm_sq] at hid
  simpa only [polarizedDerivative_add, polarizedDerivative_sub, polarizedDerivative_smul,
    polarizedDerivative_quadratic_form B hB, polarizedDerivative_quadratic_form A hA,
    hid, Q, B, A, e, harmonicHeatError] using h

include hk in
/-- The quadratic value of the operator error equals the scalar error
in every direction, not just those used in polarization. -/
theorem harmonicHeatError_energy (hρ : 0 < ρ) (hρr : ρ < r)
    {t : ℝ} (ht : 0 < t) (x : X) (v : Euclidean n) :
    ⟪v, harmonicHeatError μ hQ (k := k) G χ t x v⟫_ℝ =
      ∫ z, k t x z * cutoffSourceDensity μ hQ (G v).energy χ.sobolev χ.laplacian z ∂μ := by
  have h := harmonicHeatGram_hasDerivAt μ hQ hk G χ hρ hρr ht x (lambda := 0) le_rfl
  have hv := h.clm_apply (hasDerivAt_const t v)
  have hi := (hasDerivAt_const t v).inner ℝ hv
  simp only [inner_zero_left, map_zero, add_zero, add_apply, sub_apply,
    smul_apply, inner_add_right, inner_sub_right, inner_smul_right,
    zero_smul] at hi
  have hχΩ : tsupport (χ.weight : X → ℝ) ⊆ ball p (2 * r) := by
    intro z hz
    have hd : dist z p ≤ 2 * ρ := χ.tsupport_subset μ hQ hz
    exact lt_of_le_of_lt hd (by linarith)
  have hd := (G v).heatGram_hasDerivAt_mass μ hQ hk χ.weight
    (χ.hasCompactSupport μ hQ) hχΩ χ.sobolev χ.representative χ.laplacian
    χ.weak_laplacian p (show 0 < 2 * ρ from mul_pos (by norm_num) hρ)
    (fun z hz => χ.zero z (by simpa only [mem_closedBall, dist_comm, not_le] using hz))
    (by
      filter_upwards [χ.laplacian_locality] with z hz hn
      exact hz (Or.inr (by simpa only [mem_closedBall, dist_comm, not_le] using hn)))
    ht x 0
  have heq := hi.unique hd
  simp only [zero_mul, add_zero] at heq
  linarith

end RegularPointCoordinates

end

end OAI
