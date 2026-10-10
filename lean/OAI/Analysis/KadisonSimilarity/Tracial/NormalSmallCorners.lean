import OAI.Analysis.KadisonSimilarity.Tracial.TracialMatrixDiffuse
import OAI.Analysis.KadisonSimilarity.FreeProduct.ConcreteHaarDischarge
import OAI.Analysis.KadisonSimilarity.FreeProduct.SmallFreeCornerTransport

namespace OAI

/-! Construct small diffuse corners in the original algebra through its
actual faithful normal range, then transport the entire frame back. -/

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial UltrapowerBridge
open scoped CStarAlgebra
namespace TracialCornerGeometry

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H)
  {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Nonempty (I j)]
  (M : NestedTracialMatrices (A := I) G.trace G.vector)

local instance normalCorners_closed (N : VonNeumannAlgebra H) :
    IsClosed (N.toStarSubalgebra : Set (H →L[ℂ] H)) := base_norm_closed N

/-- The same full-matrix tower in the concrete normal coordinates. -/
def normalMatrixTower (h1 : G.trace 1 = 1) (hf : Function.Injective G.vector)
    (N : VonNeumannAlgebra H) (hN : G.left.range = N.toStarSubalgebra) :
    let τ := G.normalTracialRepresentation h1 hf N hN
    NestedTracialMatrices (A := I) (concreteTraceLinear τ) (Generator.Tracial.baseVector τ) := by
  let τ := G.normalTracialRepresentation h1 hf N hN
  let e := equivalenceOfConcreteRange N G.left (G.left_injective hf) hN
  have hv (a : P) : Generator.Tracial.baseVector τ (e a) = G.vector a := by
    change G.left a (G.vector 1) = G.vector a
    rw [G.left_vector, mul_one]
  refine {
    embedding := fun j => e.toStarAlgHom.comp (M.embedding j)
    trace_embedding := ?_
    inclusion := M.inclusion
    compatible := ?_
    dense := ?_
  }
  · intro j a
    change τ.trace (e (M.embedding j a)) = _
    rw [G.normalTracialRepresentation_trace]
    exact M.trace_embedding j a
  · intro j k h a
    change e (M.embedding k (M.inclusion j k h a)) = e (M.embedding j a)
    rw [M.compatible]
  · apply M.dense.mono
    intro ξ hξ
    obtain ⟨j, a, rfl⟩ := Set.mem_iUnion.mp hξ
    exact Set.mem_iUnion.mpr ⟨j, a, hv (M.embedding j a)⟩

include M in
/-- The normal represented source has no nonzero minimal projection. -/
theorem normalRange_diffuse_of_matrix_tower
    (h1 : G.trace 1 = 1) (hf : Function.Injective G.vector)
    (N : VonNeumannAlgebra H) (hN : G.left.range = N.toStarSubalgebra)
    (hsize : Filter.Tendsto (fun j => (Fintype.card (I j) : ℝ)) Filter.atTop Filter.atTop) :
    ∀ p : N.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
      ∃ q : N.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧
        p * q = q ∧ q * p = q := by
  let e := equivalenceOfConcreteRange N G.left (G.left_injective hf) hN
  have comparison := G.projectionComparison_of_normal_range h1 hf N hN
    (G.scalar_center_of_matrix_tower M hf)
  intro p hp hp0
  let a := e.symm p
  have ha : IsStarProjection a := hp.map e.symm
  have hea : e a = p := e.apply_symm_apply p
  have ha0 : a ≠ 0 := by
    intro h
    apply hp0
    rw [← hea, h, map_zero]
  obtain ⟨q, hq, hq0, hqa, haq, hqa'⟩ :=
    G.proper_subprojection_of_matrix_tower M hf comparison hsize a ha ha0
  refine ⟨e q, hq.map e, ?_, ?_, ?_, ?_⟩
  · intro h
    exact hq0 (e.injective (h.trans (map_zero e).symm))
  · intro h
    exact hqa (e.injective (h.trans hea.symm))
  · rw [← hea, ← map_mul, haq]
  · rw [← hea, ← map_mul, hqa']

include M in
/-- All small-frame, half-projection and Haar data are constructed together. -/
theorem exists_smallFreeCornerData_of_normal_matrix_tower
    (h1 : G.trace 1 = 1) (hf : Function.Injective G.vector)
    (N : VonNeumannAlgebra H) (hN : G.left.range = N.toStarSubalgebra)
    (hsize : Filter.Tendsto (fun j => (Fintype.card (I j) : ℝ)) Filter.atTop Filter.atTop)
    {s : ℝ} (hs : 0 < s) : Nonempty (SmallFreeCornerData G.trace s) := by
  let τ := G.normalTracialRepresentation h1 hf N hN
  let e := equivalenceOfConcreteRange N G.left (G.left_injective hf) hN
  have hdiff := G.normalRange_diffuse_of_matrix_tower M h1 hf N hN hsize
  obtain ⟨Q⟩ := exists_concreteSmallFreeCornerData_of_diffuse τ hdiff (Generator.Tracial.baseVector τ)
    (G.normalMatrixTower M h1 hf N hN) hsize hs
  have htrace (a : N.toStarSubalgebra) : G.trace (e.symm a) = concreteTraceLinear τ a := by
    have h := G.normalTracialRepresentation_trace h1 hf N hN (e.symm a)
    change τ.trace (e (e.symm a)) = G.trace (e.symm a) at h
    rw [e.apply_symm_apply] at h
    exact h.symm
  exact ⟨Q.transport e.symm.toStarAlgHom (concreteTraceLinear τ) G.trace htrace⟩

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
