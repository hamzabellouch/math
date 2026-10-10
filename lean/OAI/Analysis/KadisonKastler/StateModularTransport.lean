import OAI.Analysis.KadisonKastler.StateGraphTransport
import OAI.Analysis.KadisonKastler.ModularSpatialTransport

namespace OAI

/-! # Modular transport under a vector-state preserving isomorphism -/

namespace KadisonKastler

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}
  (θ : Algebra M ≃⋆ₐ[ℂ] Algebra N) (Ω : H) (ξ : K)
  (hM : DenseRange (algebraVectorMap M Ω))
  (hN : DenseRange (algebraVectorMap N ξ))
  (hstate : ∀ a : Algebra M, inner ℂ Ω (a.val Ω) = inner ℂ ξ ((θ a).val ξ))
  (J : H ≃ₗᵢ⋆[ℂ] H) (L : K ≃ₗᵢ⋆[ℂ] K)

theorem stateGraphUnitary_single_zero (x : H) :
    stateGraphUnitary θ Ω ξ hM hN hstate J L (Generator.tupleSingle 0 x) =
      Generator.tupleSingle 0 (statePreservingUnitary θ Ω ξ hM hN hstate x) := by
  apply PiLp.ext
  intro i
  fin_cases i
  · change stateGraphUnitary θ Ω ξ hM hN hstate J L (Generator.tupleSingle 0 x) 0 =
      Generator.tupleSingle 0 (statePreservingUnitary θ Ω ξ hM hN hstate x) 0
    rw [stateGraphUnitary_zero]
    simp only [Generator.tupleSingle_apply, Pi.single_eq_same]
  · change stateGraphUnitary θ Ω ξ hM hN hstate J L (Generator.tupleSingle 0 x) 1 =
      Generator.tupleSingle 0 (statePreservingUnitary θ Ω ξ hM hN hstate x) 1
    rw [stateGraphUnitary_one]
    simp only [Generator.tupleSingle_apply, Pi.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0),
      map_zero]

theorem statePreservingUnitary_resolvent_apply (c : ℝ) (x : H) :
    statePreservingUnitary θ Ω ξ hM hN hstate (graphResolvent M J Ω c x) =
      graphResolvent N L ξ c (statePreservingUnitary θ Ω ξ hM hN hstate x) := by
  have h := congrArg (fun v : TomitaGraphHilbert K => v 0)
    (stateGraphProjection_transport θ Ω ξ hM hN hstate J L c (Generator.tupleSingle 0 x))
  rw [stateGraphUnitary_single_zero, stateGraphUnitary_zero] at h
  exact h.symm

theorem statePreservingUnitary_resolvent (c : ℝ) :
    (statePreservingUnitary θ Ω ξ hM hN hstate).conjStarAlgEquiv (graphResolvent M J Ω c) =
      graphResolvent N L ξ c := by
  ext x
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, statePreservingUnitary_resolvent_apply,
    LinearIsometryEquiv.apply_symm_apply]

variable [TopologicalSpace.SeparableSpace H] [TopologicalSpace.SeparableSpace K]
  (hMsep : Function.Injective (algebraVectorMap M Ω))
  (hNsep : Function.Injective (algebraVectorMap N ξ))

theorem statePreservingUnitary_modular (t : Multiplicative ℝ) (x : H) :
    statePreservingUnitary θ Ω ξ hM hN hstate
        ((modularStrongGroup J Ω hMsep hM t : H →L[ℂ] H) x) =
      (modularStrongGroup L ξ hNsep hN t : K →L[ℂ] K)
        (statePreservingUnitary θ Ω ξ hM hN hstate x) :=
  modularStrongGroup_spatial J L Ω ξ hMsep hM hNsep hN
    (statePreservingUnitary θ Ω ξ hM hN hstate)
    (statePreservingUnitary_resolvent θ Ω ξ hM hN hstate J L 1) t x

end

end KadisonKastler

end OAI
