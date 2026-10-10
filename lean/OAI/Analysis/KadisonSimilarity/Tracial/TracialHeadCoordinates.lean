import OAI.Analysis.KadisonSimilarity.FreeProduct.HaarCornerLetters
import OAI.Analysis.KadisonSimilarity.Tensor.TensorHeadSlices

namespace OAI

/-! The exceptional projection in propagation, constructed from the tracial
head of the reduced-word decomposition and actual corner Haar powers. -/

noncomputable section
namespace KadisonSimilarity

variable {D P E H F : Type*} [CStarAlgebra D] [CStarAlgebra P]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Grouping reduced words by their possible initial `D` letter yields these
coordinates. The sole action field is ordinary left multiplication on that
initial tensor factor; no propagation estimate is included. -/
structure TracialHeadCoordinates (GD : TracialCornerGeometry D E)
    (G : TracialCornerGeometry P H) (ι : D →⋆ₐ[ℂ] P) (F : Type*)
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] where
  unitary : H ≃ₗᵢ[ℂ] HilbertTensor E F
  left_head : ∀ d z, unitary (G.left (ι d) z) =
    tensorHeadAction (GD.left d) (unitary z)

namespace TracialCornerGeometry

/-- The adjoint of left multiplication has the expected value on the trace
vector, providing the slicing vector without an additional hypothesis. -/
theorem left_adjoint_traceVector (G : TracialCornerGeometry P H) (a : P) :
    (G.left a).adjoint (G.vector 1) = G.vector (star a) := by
  rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star, G.left_vector, mul_one]

end TracialCornerGeometry

namespace TracialHeadCoordinates

variable {GD : TracialCornerGeometry D E} {G : TracialCornerGeometry P H}
  {ι : D →⋆ₐ[ℂ] P} (W : TracialHeadCoordinates GD G ι F)

/-- The actual exceptional subspace consists of words whose initial `D`
coordinate is the scalar trace vector. -/
abbrev vacuum : Submodule ℂ H := tracialVacuumSubspace W.unitary (GD.vector 1)

/-- Orthogonal projection onto the exceptional subspace exists by the tensor
coordinates and trace normalization. -/
theorem vacuum_hasOrthogonalProjection (hτ : GD.trace 1 = 1) :
    W.vacuum.HasOrthogonalProjection := by
  exact tracialVacuumSubspace_hasOrthogonalProjection W.unitary (GD.vector 1)
    (norm_tracialTraceVector GD.trace GD.vector GD.inner_vector hτ)

variable [W.vacuum.HasOrthogonalProjection]

/-- The exceptional component after a left letter is the tensor slice against
its adjoint applied to the trace vector. -/
theorem vacuum_slice (hτ : GD.trace 1 = 1) (d : D) (z : H) :
    W.vacuum.starProjection (G.left (ι d) z) =
      W.unitary.symm (hilbertTensorInsert (GD.vector 1)
        (tensorSlice (GD.vector (star d)) (W.unitary z))) := by
  have hΩ := norm_tracialTraceVector GD.trace GD.vector GD.inner_vector hτ
  let := vacuumSubspace_hasOrthogonalProjection (F := F) (GD.vector 1) hΩ
  have h := vacuum_slice_in_coordinates W.unitary (GD.vector 1) W.vacuum
    (G.left (ι d)) (GD.left d)
    (tracialVacuumSubspace_projection_coordinates W.unitary (GD.vector 1) hΩ)
    (W.left_head d) z
  simpa only [GD.left_adjoint_traceVector] using h

/-- A weakly null sequence of adjoint trace vectors has a vanishing exceptional
component on each fixed ambient vector. -/
theorem vacuum_tendsto_zero (hτ : GD.trace 1 = 1) (x : ℕ → D)
    (hx : Orthonormal ℂ (fun n => GD.vector (star (x n)))) (z : H) :
    Filter.Tendsto (fun n => W.vacuum.starProjection (G.left (ι (x n)) z))
      Filter.atTop (nhds 0) := by
  have ht := tensorSlice_tendsto_zero_of_orthonormal _ hx (W.unitary z)
  have hs : Filter.Tendsto (fun n => hilbertTensorInsert (GD.vector 1)
      (tensorSlice (GD.vector (star (x n))) (W.unitary z))) Filter.atTop (nhds 0) := by
    simpa only [Function.comp_def, map_zero] using
      ((hilbertTensorInsert (H := F) (GD.vector 1)).continuous.tendsto 0).comp ht
  have hu := (W.unitary.symm.continuous.tendsto 0).comp hs
  simpa only [Function.comp_def, W.vacuum_slice hτ, map_zero] using hu

/-- The normalized powers of an actual Haar unitary in a corner of `D`
therefore satisfy the exceptional-component limit used in propagation. -/
theorem haar_vacuum_tendsto_zero (hτ : GD.trace 1 = 1)
    {q : D} {hq : IsStarProjection q} (u : _root_.unitary (CStarCorner q hq))
    {a : ℝ} (ha : 0 < a) (htrace : GD.trace q = (a : ℂ))
    (hhaar : HaarCornerMoments GD.trace u a) (z : H) :
    Filter.Tendsto (fun n => W.vacuum.starProjection
      (G.left (ι (haarCornerLetter u a n)) z)) Filter.atTop (nhds 0) :=
  W.vacuum_tendsto_zero hτ _
    (GD.haarCornerLetter_adjoint_orthonormal u ha htrace hhaar) z

end TracialHeadCoordinates
end KadisonSimilarity

end

end OAI
