import OAI.Analysis.KadisonSimilarity.Tracial.NormalSmallCorners
import OAI.Analysis.KadisonSimilarity.Tracial.ConcreteRealSequence

namespace OAI

/-! The real trace-orthonormal sequence is constructed in the normal source
and transported back, so its existence need not be part of a factor model. -/

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial UltrapowerBridge
namespace TracialCornerGeometry

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H)
  {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Nonempty (I j)]
  (M : NestedTracialMatrices (A := I) G.trace G.vector)

local instance normalRealSequence_closed (N : VonNeumannAlgebra H) :
    IsClosed (N.toStarSubalgebra : Set (H →L[ℂ] H)) := base_norm_closed N

include M in
/-- The fixed matrix source supplies its own real centered sequence. -/
theorem exists_realTracialSequence_of_normal_matrix_tower
    (h1 : G.trace 1 = 1) (hf : Function.Injective G.vector)
    (N : VonNeumannAlgebra H) (hN : G.left.range = N.toStarSubalgebra)
    (hsize : Filter.Tendsto (fun j => (Fintype.card (I j) : ℝ)) Filter.atTop Filter.atTop) :
    Nonempty (RealTracialSequence G.trace) := by
  let τ := G.normalTracialRepresentation h1 hf N hN
  let e := equivalenceOfConcreteRange N G.left (G.left_injective hf) hN
  let S := concreteRealTracialSequence τ
    (G.normalRange_diffuse_of_matrix_tower M h1 hf N hN hsize)
  have ht (a : N.toStarSubalgebra) : G.trace (e.symm a) = concreteTraceLinear τ a := by
    have h := G.normalTracialRepresentation_trace h1 hf N hN (e.symm a)
    change τ.trace (e (e.symm a)) = G.trace (e.symm a) at h
    rw [e.apply_symm_apply] at h
    exact h.symm
  refine ⟨{
    vector := fun n => e.symm (S.vector n)
    trace_zero := ?_
    selfadjoint := ?_
    inner := ?_ }⟩
  · intro n
    rw [ht]
    exact S.trace_zero n
  · intro n
    have hs : e.symm (star (S.vector n)) = star (e.symm (S.vector n)) :=
      e.symm.map_star' _
    rw [← hs, S.selfadjoint]
  · intro n m
    have hs : e.symm (star (S.vector n)) = star (e.symm (S.vector n)) :=
      e.symm.map_star' _
    have hm : e.symm (star (S.vector n) * S.vector m) =
        e.symm (star (S.vector n)) * e.symm (S.vector m) := e.symm.map_mul' _ _
    rw [← hs, ← hm, ht]
    exact S.inner n m

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
