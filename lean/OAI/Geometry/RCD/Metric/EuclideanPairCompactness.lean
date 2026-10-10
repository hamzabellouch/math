import OAI.Geometry.RCD.Transport.GeodesicPlanTightness

namespace OAI

/-! # A common subsequence for bounded Euclidean endpoint-pair laws -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal Topology
noncomputable section
namespace RegularPointCoordinates

theorem euclidean_pair_subsequence {n : ℕ}
    (νs : ℕ → ProbabilityMeasure (Euclidean n × Euclidean n)) (B : ℝ)
    (hb : ∀ k, ∀ᵐ z ∂(νs k : Measure (Euclidean n × Euclidean n)),
      z∈closedBall (0:Euclidean n) B ×ˢ closedBall (0:Euclidean n) B) :
    ∃ ν : ProbabilityMeasure (Euclidean n × Euclidean n), ∃ t : ℕ → ℕ,
      StrictMono t ∧ Tendsto (νs ∘ t) atTop (𝓝 ν) ∧
      ∀ᵐ z ∂(ν : Measure (Euclidean n × Euclidean n)),
        z∈closedBall (0:Euclidean n) B ×ˢ closedBall (0:Euclidean n) B := by
  let A := closedBall (0:Euclidean n) B ×ˢ closedBall (0:Euclidean n) B
  have hA : IsCompact A := (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  have hνs (k : ℕ) : (νs k : Measure (Euclidean n × Euclidean n)) Aᶜ=0 := ae_iff.mp (hb k)
  have hT : IsTightMeasureSet {((ν : ProbabilityMeasure (Euclidean n × Euclidean n)) :
      Measure (Euclidean n × Euclidean n)) | ν∈range νs} := by
    apply isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mpr
    intro ε hε
    refine ⟨A,hA,?_⟩
    rintro μ ⟨ν,⟨k,rfl⟩,rfl⟩
    exact (hνs k).le.trans hε.le
  have hC := isCompact_closure_of_isTightMeasureSet hT
  obtain ⟨ν,_,t,ht,hlim⟩ := hC.tendsto_subseq (fun k => subset_closure (mem_range_self k))
  refine ⟨ν,t,ht,hlim,?_⟩
  apply ae_iff.mpr
  change (ν : Measure (Euclidean n × Euclidean n)) Aᶜ=0
  have hh := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim hA.isClosed.isOpen_compl
  have hz : (fun k => ((νs ∘ t) k : Measure (Euclidean n × Euclidean n)) Aᶜ)=fun _ => 0 :=
    funext fun k => hνs (t k)
  simpa only [hz,liminf_const,le_zero_iff] using hh

end RegularPointCoordinates

end

end OAI
