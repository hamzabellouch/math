import OAI.Analysis.KadisonKastler.TomitaGraphClosability
import Mathlib.Analysis.InnerProductSpace.LinearPMap

namespace OAI

/-! # The closed Tomita operator in linear coordinates

The fixed antiunitary in the second coordinate turns the Tomita operator
into a complex-linear, densely defined closed operator. Its graph is the
previously constructed closed graph, not an assumed modular object.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

/-- Changing only the finite product norm does not change the graph topology. -/
def tomitaProductCoordinates : TomitaGraphHilbert H ≃L[ℂ] H × H :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 2 => H)).trans
    (ContinuousLinearEquiv.finTwoArrow ℂ H)

/-- The closed graph in the ordinary product used by `LinearPMap`. -/
def tomitaProductGraph (M : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H)
    (Ω : H) (c : ℝ) : Submodule ℂ (H × H) :=
  (rescaledGraphSubspace M J Ω c).comap tomitaProductCoordinates.symm.toLinearMap

theorem tomitaProductGraph_closed (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ) :
    IsClosed (tomitaProductGraph M J Ω c : Set (H × H)) :=
  (rescaledGraphMap M J Ω c).range.isClosed_topologicalClosure.preimage
    tomitaProductCoordinates.symm.continuous

theorem tomitaProductGraph_no_vertical (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (x : H × H) (hx : x ∈ tomitaProductGraph M J Ω c) (hzero : x.1 = 0) :
    x.2 = 0 := by
  have h := rescaledGraph_no_vertical J Ω c hsep
    (tomitaProductCoordinates.symm x) hx hzero
  exact congrArg (fun v : TomitaGraphHilbert H => v 1) h

/-- The actual closed operator, expressed using a fixed conjugate copy of H. -/
def tomitaClosedLinearOperator (M : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H)
    (Ω : H) (c : ℝ) : H →ₗ.[ℂ] H :=
  (tomitaProductGraph M J Ω c).toLinearPMap

theorem tomitaClosedLinearOperator_graph (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ)
    (hsep : Function.Injective (algebraVectorMap M Ω)) :
    (tomitaClosedLinearOperator M J Ω c).graph = tomitaProductGraph M J Ω c :=
  (tomitaProductGraph M J Ω c).toLinearPMap_graph_eq
    (tomitaProductGraph_no_vertical J Ω c hsep)

theorem tomitaClosedLinearOperator_closed (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ)
    (hsep : Function.Injective (algebraVectorMap M Ω)) :
    (tomitaClosedLinearOperator M J Ω c).IsClosed := by
  rw [LinearPMap.IsClosed, tomitaClosedLinearOperator_graph J Ω c hsep]
  exact tomitaProductGraph_closed J Ω c

theorem tomitaClosedLinearOperator_algebraic_graph (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (c : ℝ) (hsep : Function.Injective (algebraVectorMap M Ω)) (a : Algebra M) :
    (a.val Ω, c • J (star a.val Ω)) ∈ (tomitaClosedLinearOperator M J Ω c).graph := by
  rw [tomitaClosedLinearOperator_graph J Ω c hsep]
  exact rescaledGraphVector_mem M J Ω c a

theorem tomitaClosedLinearOperator_dense (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) :
    Dense ((tomitaClosedLinearOperator M J Ω c).domain : Set H) := by
  apply hcyc.mono
  rintro _ ⟨a, rfl⟩
  obtain ⟨x, hx, _⟩ := (LinearPMap.mem_graph_iff _).mp
    (tomitaClosedLinearOperator_algebraic_graph J Ω c hsep a)
  change a.val Ω ∈ (tomitaClosedLinearOperator M J Ω c).domain
  change x.val = a.val Ω at hx
  rw [← hx]
  exact x.property

end

end KadisonKastler

end OAI
