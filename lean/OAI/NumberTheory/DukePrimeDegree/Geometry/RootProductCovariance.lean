import OAI.NumberTheory.DukePrimeDegree.Geometry.NormalizedPiMeasures
import OAI.NumberTheory.PrimePackets.AmbientLeaves

namespace OAI

/-! # Diagonal covariance of the actual product of root leaves

The normalization is on the unit rectangle. No independence or
conditional-entropy identification is assumed in this calculation.
-/

noncomputable section
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

private lemma locallyFinite_map_real (ν : Measure ℝ) [IsLocallyFiniteMeasure ν]
    (E : ℝ ≃ₜ ℝ) : IsLocallyFiniteMeasure (ν.map E) := by
  constructor
  intro x
  obtain ⟨U, hx, hU, hfin⟩ := Measure.exists_isOpen_measure_lt_top ν (E.symm x)
  refine ⟨E '' U, (E.isOpenMap _ hU).mem_nhds ⟨E.symm x, hx, E.apply_symm_apply x⟩, ?_⟩
  rw [Measure.map_apply E.measurable (E.isOpenMap _ hU).measurableSet,
    E.injective.preimage_image]
  exact hfin

theorem ae_rootProduct_diagonal {ι : Type*} [Fintype ι]
    (d : ℕ) (i j : ι → Fin (d+1)) (hij : ∀ a, i a ≠ j a)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ k, ell k = 0) (t : ℝ) :
    ∀ᵐ x ∂μ,
      (Measure.pi fun a => intrinsicRootLeaf (hij a) μ
        (rightAction x (diagonalOneParameter ell hell t))) =
      anchorNormalize
        ((Measure.pi fun a => intrinsicRootLeaf (hij a) μ x).map
          (fun v a => rootTimeScaling ell (i a) (j a) t (v a)))
        (Set.univ.pi fun _ : ι => Metric.ball 0 1) := by
  have hfree (a : ι) : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection (hij a) v) = x → v = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun _ hx => hx (i a) (j a) (hij a)
  have hinv : μ.map (fun x => rightAction x (diagonalOneParameter ell hell t)) = μ := by
    rw [diagonalOneParameter_eq_diagonalFlow ell hell t]
    exact hA _
  have hcov := ae_all_iff.mpr (fun a =>
    ae_intrinsicRootLeaf_diagonal (hij a) ell hell t μ (hfree a) hinv)
  have hspec := ae_all_iff.mpr (fun a => ae_intrinsicRootLeaf_spec (hij a) μ (hfree a))
  have hpos := ae_all_iff.mpr (fun a => ae_intrinsicRootLeaf_ball_pos (hij a) μ (hfree a))
  filter_upwards [hcov, hspec, hpos] with x hx hs hp
  let ν : ι → Measure ℝ := fun a => intrinsicRootLeaf (hij a) μ x
  let F (a : ι) := rootTimeScaling ell (i a) (j a) t
  let : ∀ a, IsLocallyFiniteMeasure (ν a) := fun a => (hs a).1
  let : ∀ a, IsLocallyFiniteMeasure ((ν a).map (F a)) :=
    fun a => locallyFinite_map_real (ν a) (F a)
  have hmass (a : ι) : (ν a).map (F a) (Metric.ball 0 1) ≠ 0 := by
    rw [Measure.map_apply (F a).measurable isOpen_ball.measurableSet]
    change ν a ((Homeomorph.mulLeft₀ _ _) ⁻¹' Metric.ball 0 1) ≠ 0
    rw [realScaling_preimage_ball _ _ (Real.exp_pos _)]
    exact (hp a _ (by positivity)).ne'
  calc
    _ = Measure.pi (fun a => anchorNormalize ((ν a).map (F a)) (Metric.ball 0 1)) := by
      congr 1
      funext a
      exact hx a
    _ = anchorNormalize (Measure.pi fun a => (ν a).map (F a))
        (Set.univ.pi fun _ : ι => Metric.ball 0 1) :=
      pi_anchorNormalize _ _ hmass
    _ = _ := by
      rw [Measure.pi_map_pi (fun a => (F a).measurable.aemeasurable)]

end DukePrimeDegree

end

end OAI
