import OAI.Analysis.OperatorAlgebra.IntertwinerCompression
import OAI.Analysis.OperatorAlgebra.IsometricCornerOperators
import OAI.Analysis.ModularRecovery.TomitaFundamental

namespace OAI

/-! A separating vector remains separating on its cyclic subrepresentation.
The proof compresses the actual commuting operators and uses their dense
orbit, rather than assuming the compressed bicommutant is a normal image. -/
noncomputable section
open scoped Topology
namespace WeakPureInfiniteness
open BoundedRecovery

variable {A H K : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma separating_compression (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (W : K →ₗᵢ[ℂ] H)
    (hW : ∀ a, W.toContinuousLinearMap.comp (ρ a) = (π a).comp W.toContinuousLinearMap)
    (M : VonNeumannAlgebra H) (hπ : ∀ a, π a ∈ M) (ξ : K)
    (hsep : ∀ T : H →L[ℂ] H, T ∈ M → T (W ξ) = 0 → T = 0)
    (U : K →L[ℂ] K)
    (hU : ∀ R : K →L[ℂ] K, (∀ a, Commute (ρ a) R) → Commute R U)
    (hzero : U ξ = 0) : U = 0 := by
  have hd := commutant_cyclic M (W ξ) hsep
  have hv (x : H) : U (W.toContinuousLinearMap.adjoint x) = 0 := by
    apply closure_minimal (s := (operatorOrbit M.commutant (W ξ) : Set H)) ?_
      (isClosed_eq (U.continuous.comp W.toContinuousLinearMap.adjoint.continuous)
        continuous_const) (hd x)
    rintro _ ⟨T, hT, rfl⟩
    have hTπ (a : A) : Commute (π a) T :=
      VonNeumannAlgebra.mem_commutant_iff.mp hT (π a) (hπ a)
    have hc := hU (isometricCornerCompress W T)
      (fun a => intertwiner_compression_commutes ρ π W.toContinuousLinearMap hW T hTπ a)
    have he := congrArg (fun V : K →L[ℂ] K => V ξ) hc.eq
    change W.toContinuousLinearMap.adjoint (T (W (U ξ))) =
      U (W.toContinuousLinearMap.adjoint (T (W ξ))) at he
    rw [hzero, map_zero, map_zero, map_zero] at he
    exact he.symm
  apply ContinuousLinearMap.ext
  intro x
  have he := hv (W x)
  rwa [isometricCorner_adjoint_apply] at he

end WeakPureInfiniteness

end

end OAI
