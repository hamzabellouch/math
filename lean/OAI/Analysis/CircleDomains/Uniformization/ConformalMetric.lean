import OAI.Analysis.CircleDomains.Sobolev.SupportedMetric

namespace OAI

/-!
# Restoring the spherical metric factor

In two dimensions positive scalar rescaling leaves the full Dirichlet
energy density unchanged. Thus a compactly supported metric modification
in a planar chart can retain the original spherical factor both near
the core and outside a compact set.
-/

open Matrix Set Filter MeasureTheory Metric
open scoped Topology ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem matrixEnergy_pos_smul (A : PlanarMetric) {g : PlanarMetric}
    (hg : g.PosDef) {c : ℝ} (hc : 0 < c) :
    matrixEnergy A (c • g) = matrixEnergy A g := by
  let : Invertible c := invertibleOfNonzero hc.ne'
  have hinv : (c • g)⁻¹ = c⁻¹ • g⁻¹ := by
    simpa only [invOf_eq_inv] using Matrix.inv_smul (A := g) c
      (isUnit_iff_ne_zero.mpr hg.det_pos.ne')
  unfold matrixEnergy
  rw [hinv, smul_mul_assoc, Matrix.trace_smul, Matrix.det_smul]
  simp only [Fintype.card_fin, smul_eq_mul]
  rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le]
  field_simp

def sphericalMetricFactor (z : ℝ × ℝ) : ℝ :=
  4 / (1 + z.1 ^ 2 + z.2 ^ 2) ^ 2

theorem sphericalMetricFactor_pos (z : ℝ × ℝ) : 0 < sphericalMetricFactor z := by
  unfold sphericalMetricFactor
  positivity

theorem contDiff_sphericalMetricFactor : ContDiff ℝ ∞ sphericalMetricFactor := by
  unfold sphericalMetricFactor
  apply ContDiff.div contDiff_const
  · fun_prop
  · intro z
    positivity

/-- Small energy for the actual spherical background factor, with exact
agreement near an arbitrary closed retained core and near infinity. -/
theorem exists_supported_spherical_metric_for_coordinates
    (f : ℕ → (ℝ × ℝ) → ℝ) (n : ℕ) {Ω Q K : Set (ℝ × ℝ)}
    (hΩ : IsOpen Ω) (hQ : IsCompact Q) (hQΩ : Q ⊆ Ω)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) Ω) (hK : IsClosed K) {ε : ℝ}
    (hε : (∫ z in Q \ K, 2 * coordinateWedges f n z) < ε) :
    ∃ (R : ℝ) (g : (ℝ × ℝ) → PlanarMetric), 0 < R ∧ ContDiff ℝ ∞ g ∧
      (∀ z, (g z).PosDef) ∧
      (∀ᶠ z in 𝓝ˢ K, g z = sphericalMetricFactor z • 1) ∧
      (∀ z ∉ closedBall 0 R, g z = sphericalMetricFactor z • 1) ∧
      (∫ z in Q \ K, matrixEnergy (coordinateGram f n z) (g z)) < ε := by
  obtain ⟨R, g, hR, hg, hPD, hcore, hfar, henergy⟩ :=
    exists_supported_metric_for_local_coordinates f n hΩ hQ hQΩ hf hK hε
  refine ⟨R, fun z => sphericalMetricFactor z • g z, hR,
    contDiff_sphericalMetricFactor.smul hg,
    fun z => (hPD z).smul (sphericalMetricFactor_pos z), ?_, ?_, ?_⟩
  · filter_upwards [hcore] with z hz
    rw [hz]
  · intro z hz
    change sphericalMetricFactor z • g z = _
    rw [hfar z hz]
  · simpa only [matrixEnergy_pos_smul _ (hPD _) (sphericalMetricFactor_pos _)] using henergy

end CircleDomainRigidity.FiniteTransfer

end

end OAI
