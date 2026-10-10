import OAI.Geometry.SurfaceImmersion.Geometry.FlatFirstNull

namespace OAI

/-! Linear coordinate changes preserve null sets, including between the
finite-dimensional models used in the Sard argument. -/
noncomputable section
open Set MeasureTheory
open scoped Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace F] [BorelSpace F]

theorem linear_equiv_null_image (e : E ≃L[ℝ] F)
    (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    (ν : Measure F) [Measure.IsAddHaarMeasure ν]
    {s : Set E} (hs : μ s = 0) : ν (e '' s) = 0 := by
  have hm : ν.map e.symm ≪ μ :=
    Measure.absolutelyContinuous_isAddHaarMeasure (ν.map e.symm) μ
  have hz := hm hs
  have he : MeasurableEmbedding (e.symm : F → E) := e.symm.toHomeomorph.measurableEmbedding
  rw [he.map_apply] at hz
  simpa only [e.image_eq_preimage_symm] using hz

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
