import Mathlib.Tactic.Linarith
import Mathlib.Topology.MetricSpace.HausdorffDistance

namespace OAI

noncomputable section

/- Distance sublevels for sets with dense continuous sections.
   In the relative-generation application, the sections are coefficient-polynomial vectors. -/
open scoped Topology
namespace Generator.RelativeCompletion
variable {E X I : Type*} [PseudoMetricSpace E]

theorem infDist_lt_iff_dense_sections
    (L : X → Set E) (b : I → X → E)
    (hb : ∀ i x, b i x ∈ L x)
    (hd : ∀ x, DenseRange (fun i => (⟨b i x, hb i x⟩ : L x)))
    (hne : ∀ x, (L x).Nonempty) (ξ : E) (x : X) (ε : ℝ) :
    Metric.infDist ξ (L x) < ε ↔ ∃ i, dist ξ (b i x) < ε := by
  constructor
  · intro h
    obtain ⟨y, hy, hdist⟩ := (Metric.infDist_lt_iff (hne x)).mp h
    obtain ⟨i, hi⟩ := (hd x).exists_dist_lt ⟨y,hy⟩ (sub_pos.mpr hdist)
    refine ⟨i, ?_⟩
    have ht := dist_triangle ξ y (b i x)
    have hi' : dist y (b i x) < ε - dist ξ y := hi
    linarith
  · rintro ⟨i,hi⟩
    exact (Metric.infDist_le_dist_of_mem (hb i x)).trans_lt hi

variable [TopologicalSpace X]

theorem isOpen_infDist_lt_dense_sections
    (L : X → Set E) (b : I → X → E)
    (hb : ∀ i x, b i x ∈ L x)
    (hc : ∀ i, Continuous (b i))
    (hd : ∀ x, DenseRange (fun i => (⟨b i x, hb i x⟩ : L x)))
    (hne : ∀ x, (L x).Nonempty) (ξ : E) (ε : ℝ) :
    IsOpen {x | Metric.infDist ξ (L x) < ε} := by
  have he : {x | Metric.infDist ξ (L x) < ε} =
      ⋃ i, {x | dist ξ (b i x) < ε} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    exact infDist_lt_iff_dense_sections L b hb hd hne ξ x ε
  rw [he]
  exact isOpen_iUnion fun i => isOpen_lt (continuous_const.dist (hc i)) continuous_const

end Generator.RelativeCompletion

end

end OAI
