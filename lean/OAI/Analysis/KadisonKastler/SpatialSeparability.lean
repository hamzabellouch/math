import OAI.Analysis.KadisonKastler.SpatialProductCyclic
import Mathlib.Topology.Algebra.Module.Basic

namespace OAI

/-! # Separability of the completed spatial tensor product -/

namespace KadisonKastler

open UnitalTomsWinter

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace H] [CompleteSpace K] in
/-- A countable dense family in each leg gives a countable total family
of pure tensors in the completed Hilbert tensor product. -/
theorem dense_span_tensorVector {f : ℕ → H} {g : ℕ → K}
    (hf : DenseRange f) (hg : DenseRange g) :
    Dense (Submodule.span ℂ (Set.range (fun p : ℕ × ℕ => tensorVector (g p.2) (f p.1))) :
      Set (SpatialHilbert H K)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff]
  apply bot_unique
  intro v hv
  change v = 0
  apply spatialTensor_vector_ext
  intro x y
  rw [inner_zero_right]
  have hfinite (i j : ℕ) : inner ℂ (tensorVector (g j) (f i)) v = 0 :=
    hv _ (Submodule.subset_span ⟨(i, j), rfl⟩)
  have hy (i : ℕ) : inner ℂ (tensorVector y (f i)) v = 0 := by
    refine hg.induction_on (p := fun z => inner ℂ (tensorVector z (f i)) v = 0) y ?_ ?_
    · change IsClosed {z : K | inner ℂ (leftTensorVector (f i) z) v = 0}
      exact isClosed_eq (by fun_prop) continuous_const
    · exact hfinite i
  change inner ℂ (tensorVector y x) v = 0
  refine hf.induction_on (p := fun z => inner ℂ (tensorVector y z) v = 0) x ?_ ?_
  · exact isClosed_eq (by fun_prop) continuous_const
  · exact hy

instance spatialHilbert_separable [TopologicalSpace.SeparableSpace H]
    [TopologicalSpace.SeparableSpace K] : TopologicalSpace.SeparableSpace (SpatialHilbert H K) := by
  let f := TopologicalSpace.denseSeq H
  let g := TopologicalSpace.denseSeq K
  have hd := dense_span_tensorVector (TopologicalSpace.denseRange_denseSeq H)
    (TopologicalSpace.denseRange_denseSeq K)
  apply hd.isSeparable_iff.mp
  exact (Set.countable_range (fun p : ℕ × ℕ => tensorVector (g p.2) (f p.1))).isSeparable.span
    (R := ℂ)

/-- A pair of nonzero vectors witnesses nontriviality after completion. -/
instance spatialHilbert_nontrivial [Nontrivial H] [Nontrivial K] :
    Nontrivial (SpatialHilbert H K) := by
  obtain ⟨x, hx⟩ := exists_ne (0 : H)
  obtain ⟨y, hy⟩ := exists_ne (0 : K)
  refine ⟨⟨tensorVector y x, 0, ?_⟩⟩
  intro he
  have hn := congrArg norm he
  rw [norm_tensorVector_apply, norm_zero] at hn
  exact (mul_ne_zero (norm_ne_zero_iff.mpr hx) (norm_ne_zero_iff.mpr hy)) hn

end

end KadisonKastler

end OAI
