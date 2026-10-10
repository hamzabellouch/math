import OAI.Analysis.CircleDomains.Sobolev.LocalCoordinateMetric

namespace OAI

/-!
# Metric changes with compact support

The original core may be unbounded in a planar chart, as happens when
the retained spherical core contains infinity. Only its intersection
with a compact neighborhood of the completed piece is needed for the
interpolation. A second cutoff keeps the metric unchanged at infinity.
-/

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff Manifold Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

@[simp] theorem blendMetric_identity (t : ℝ) : blendMetric 1 t = 1 := by
  rw [blendMetric, ← add_smul]
  simp

theorem exists_supported_metric_for_local_coordinates
    (f : ℕ → (ℝ × ℝ) → ℝ) (n : ℕ) {Ω Q K : Set (ℝ × ℝ)}
    (hΩ : IsOpen Ω) (hQ : IsCompact Q) (hQΩ : Q ⊆ Ω)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) Ω) (hK : IsClosed K) {ε : ℝ}
    (hε : (∫ z in Q \ K, 2 * coordinateWedges f n z) < ε) :
    ∃ (R : ℝ) (g : (ℝ × ℝ) → PlanarMetric), 0 < R ∧ ContDiff ℝ ∞ g ∧
      (∀ z, (g z).PosDef) ∧ (∀ᶠ z in 𝓝ˢ K, g z = 1) ∧
      (∀ z ∉ closedBall 0 R, g z = 1) ∧
      (∫ z in Q \ K, matrixEnergy (coordinateGram f n z) (g z)) < ε := by
  obtain ⟨R, hR, hQR⟩ := hQ.isBounded.exists_pos_norm_lt
  have hQB : Q ⊆ ball 0 R := fun z hz => by
    simpa only [mem_ball, dist_zero_right] using hQR z hz
  let L := K ∩ closedBall 0 R
  have hL : IsCompact L := (isCompact_closedBall (0 : ℝ × ℝ) R).of_isClosed_subset
    (hK.inter isClosed_closedBall) inter_subset_right
  have hdiff : Q \ L = Q \ K := by
    ext z
    constructor
    · intro hz
      exact ⟨hz.1, fun hzK => hz.2 ⟨hzK, ball_subset_closedBall (hQB hz.1)⟩⟩
    · exact fun hz => ⟨hz.1, fun hzL => hz.2 hzL.1⟩
  obtain ⟨τ, N, g₀, _, _, _, _, hg₀, hPD₀, hcore, _, henergy⟩ :=
    exists_metric_for_local_coordinates f n hΩ hQ hQΩ hf hL isOpen_univ (subset_univ _)
      (hdiff.symm ▸ hε)
  obtain ⟨ψ, hzero, hone, hψrange⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    (𝓘(ℝ, ℝ × ℝ)) isOpen_ball.isClosed_compl hQ.isClosed
      (disjoint_compl_left_iff_subset.mpr hQB) (n := (⊤ : ℕ∞))
  have hψ : ContDiff ℝ ∞ (ψ : (ℝ × ℝ) → ℝ) := contMDiff_iff_contDiff.mp ψ.contMDiff
  let g : (ℝ × ℝ) → PlanarMetric := fun z => blendMetric (g₀ z) (ψ z)
  have hg : ContDiff ℝ ∞ g :=
    ((contDiff_const.sub hψ).smul contDiff_const).add (hψ.smul hg₀)
  have heqQ {z : ℝ × ℝ} (hz : z ∈ Q) : g z = g₀ z := by
    dsimp only [g]
    rw [hone.self_of_nhdsSet z hz, blendMetric_one]
  refine ⟨R, g, hR, hg, fun z => blendMetric_posDef (hPD₀ z) (hψrange z), ?_, ?_, ?_⟩
  · apply eventually_nhdsSet_iff_forall.mpr
    intro z hz
    by_cases hzB : z ∈ closedBall 0 R
    · filter_upwards [hcore.filter_mono (nhds_le_nhdsSet (show z ∈ L from ⟨hz, hzB⟩))]
        with w hw
      simp only [g, hw, blendMetric_identity]
    · have hzout : z ∈ (ball 0 R)ᶜ := fun hb => hzB (ball_subset_closedBall hb)
      filter_upwards [hzero.filter_mono (nhds_le_nhdsSet hzout)] with w hw
      simp only [g, hw, blendMetric_zero]
  · intro z hz
    have hzout : z ∈ (ball 0 R)ᶜ := fun hb => hz (ball_subset_closedBall hb)
    simp only [g, hzero.self_of_nhdsSet z hzout, blendMetric_zero]
  · rw [hdiff] at henergy
    have heq : (∫ z in Q \ K, matrixEnergy (coordinateGram f n z) (g z)) =
        ∫ z in Q \ K, matrixEnergy (coordinateGram f n z) (g₀ z) :=
      setIntegral_congr_fun (hQ.isClosed.measurableSet.diff hK.measurableSet)
        (fun z hz => congrArg (matrixEnergy (coordinateGram f n z)) (heqQ hz.1))
    exact heq.trans_lt henergy

end CircleDomainRigidity.FiniteTransfer

end

end OAI
