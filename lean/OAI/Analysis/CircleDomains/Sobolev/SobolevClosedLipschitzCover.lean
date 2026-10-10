import OAI.Analysis.CircleDomains.Sobolev.SquareOscillationLipschitz
import OAI.Analysis.CircleDomains.Sobolev.SquareAverageBounded
import OAI.Analysis.CircleDomains.Sobolev.CompactWeakDerivativeIntegral

namespace OAI

/-! Countably many closed Lipschitz pieces cover almost every point of a
continuous Sobolev representative with integrable partials. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity

lemma exists_closed_lipschitz_cover_of_integrable_partials {u : EuclideanPlane → ℝ}
    (hu : Continuous u) {V : EuclideanPlane → EuclideanPlane}
    (hw : DeGiorgi.HasWeakGrad V u univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (ball 0 R)))
    (hI : Integrable (fun p : ℝ × ℝ =>
      |V (euclideanPlaneCoordinates.symm p) 0|+|V (euclideanPlaneCoordinates.symm p) 1|) volume) :
    ∃ K : ℕ → Set (ℝ × ℝ),
      (∀ n, IsClosed (K n) ∧
        LipschitzOnWith (64*(n:ℝ≥0)) (fun p => u (euclideanPlaneCoordinates.symm p)) (K n)) ∧
      ∀ᵐ p ∂volume, p ∈ ⋃ n, K n := by
  let g : ℝ × ℝ → ℝ := fun p =>
    |V (euclideanPlaneCoordinates.symm p) 0|+|V (euclideanPlaneCoordinates.symm p) 1|
  let S : ℕ → Set (ℝ × ℝ) := fun n => {c | ∀ r > 0, squareAverage g c r ≤ n}
  refine ⟨fun n => closure (S n), ?_, ?_⟩
  · intro n
    refine ⟨isClosed_closure, ?_⟩
    apply LipschitzOnWith.closure (hu.comp euclideanPlaneCoordinates.symm.continuous).continuousOn
    exact locally_sobolev_lipschitzOn_of_square_averages hu hw hLp (n:ℝ≥0) (fun c hc => hc)
  · filter_upwards [ae_squareAverage_bounded hI] with p hp
    obtain ⟨B, _, hB⟩ := hp
    obtain ⟨n, hn⟩ := exists_nat_ge B
    apply mem_iUnion.mpr
    refine ⟨n, subset_closure ?_⟩
    intro r hr
    exact (hB r hr).trans hn

lemma compact_sobolev_closed_lipschitz_cover {u : EuclideanPlane → ℝ}
    (hu : Continuous u) (hs : HasCompactSupport u) (W : DeGiorgi.MemW1pWitness 2 u univ) :
    ∃ K : ℕ → Set (ℝ × ℝ),
      (∀ n, IsClosed (K n) ∧
        LipschitzOnWith (64*(n:ℝ≥0)) (fun p => u (euclideanPlaneCoordinates.symm p)) (K n)) ∧
      ∀ᵐ p ∂volume, p ∈ ⋃ n, K n := by
  have hLp (R : ℝ) (i : Fin 2) :
      MemLp (fun p => W.weakGrad p i) 2 (volume.restrict (ball 0 R)) := by
    have h : MemLp (fun p => W.weakGrad p i) 2 volume := by
      simpa only [Measure.restrict_univ] using W.weakGrad_component_memLp i
    exact h.restrict _
  have hI (i : Fin 2) : Integrable (fun p : ℝ × ℝ => W.weakGrad (euclideanPlaneCoordinates.symm p) i)
      volume := euclideanPlaneCoordinates_symm_measurePreserving.integrable_comp_of_integrable
        (compact_weakGradient_integrable W hs i)
  exact exists_closed_lipschitz_cover_of_integrable_partials hu W.isWeakGrad hLp ((hI 0).abs.add (hI 1).abs)

end CircleDomainRigidity

end

end OAI
