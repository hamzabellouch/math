import OAI.Analysis.KadisonKastler.StatePreservingSpatial
import OAI.Analysis.KadisonKastler.GraphIdentificationIndependence

namespace OAI

/-! # Transporting the closed Tomita graph under a state isomorphism -/

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

def stateGraphUnitary : TomitaGraphHilbert H ≃ₗᵢ[ℂ] TomitaGraphHilbert K :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun i : Fin 2 =>
    if i = 0 then statePreservingUnitary θ Ω ξ hM hN hstate
    else (J.symm.trans (statePreservingUnitary θ Ω ξ hM hN hstate)).trans L)

theorem stateGraphUnitary_zero (v : TomitaGraphHilbert H) :
    stateGraphUnitary θ Ω ξ hM hN hstate J L v 0 =
      statePreservingUnitary θ Ω ξ hM hN hstate (v 0) := by
  change (if (0 : Fin 2) = 0 then statePreservingUnitary θ Ω ξ hM hN hstate
    else (J.symm.trans (statePreservingUnitary θ Ω ξ hM hN hstate)).trans L) (v 0) = _
  rw [ite_eq_left rfl]

theorem stateGraphUnitary_one (v : TomitaGraphHilbert H) :
    stateGraphUnitary θ Ω ξ hM hN hstate J L v 1 =
      L (statePreservingUnitary θ Ω ξ hM hN hstate (J.symm (v 1))) := by
  change (if (1 : Fin 2) = 0 then statePreservingUnitary θ Ω ξ hM hN hstate
    else (J.symm.trans (statePreservingUnitary θ Ω ξ hM hN hstate)).trans L) (v 1) = _
  rw [ite_eq_right (by decide)]
  rfl

theorem stateGraphUnitary_vector (c : ℝ) (a : Algebra M) :
    stateGraphUnitary θ Ω ξ hM hN hstate J L (rescaledGraphVector J Ω c a.val) =
      rescaledGraphVector L ξ c (θ a).val := by
  apply PiLp.ext
  intro i
  fin_cases i
  · change stateGraphUnitary θ Ω ξ hM hN hstate J L (rescaledGraphVector J Ω c a.val) 0 =
      rescaledGraphVector L ξ c (θ a).val 0
    rw [stateGraphUnitary_zero, rescaledGraphVector_zero, rescaledGraphVector_zero]
    exact statePreservingUnitary_algebraVector θ Ω ξ hM hN hstate a
  · change stateGraphUnitary θ Ω ξ hM hN hstate J L (rescaledGraphVector J Ω c a.val) 1 =
      rescaledGraphVector L ξ c (θ a).val 1
    rw [stateGraphUnitary_one, rescaledGraphVector_one, rescaledGraphVector_one]
    simp only [← Complex.coe_smul]
    rw [J.symm.map_smulₛₗ, Complex.conj_ofReal, J.symm_apply_apply, map_smul,
      L.map_smulₛₗ, Complex.conj_ofReal]
    congr 1
    have h := statePreservingUnitary_algebraVector θ Ω ξ hM hN hstate (star a)
    have hs : θ (star a) = star (θ a) := map_star θ a
    rw [hs] at h
    exact congrArg L h

theorem stateGraphUnitary_mem (c : ℝ) {v : TomitaGraphHilbert H}
    (hv : v ∈ rescaledGraphSubspace M J Ω c) :
    stateGraphUnitary θ Ω ξ hM hN hstate J L v ∈ rescaledGraphSubspace N L ξ c := by
  let W := stateGraphUnitary θ Ω ξ hM hN hstate J L
  have hc : IsClosed {v : TomitaGraphHilbert H | W v ∈ rescaledGraphSubspace N L ξ c} :=
    (Submodule.isClosed_topologicalClosure _).preimage W.continuous
  apply closure_minimal (s := Set.range (rescaledGraphMap M J Ω c)) ?_ hc hv
  rintro _ ⟨a, rfl⟩
  change W (rescaledGraphVector J Ω c a.val) ∈ rescaledGraphSubspace N L ξ c
  rw [stateGraphUnitary_vector]
  exact rescaledGraphVector_mem N L ξ c (θ a)

theorem stateGraphUnitary_symm_mem (c : ℝ) {v : TomitaGraphHilbert K}
    (hv : v ∈ rescaledGraphSubspace N L ξ c) :
    (stateGraphUnitary θ Ω ξ hM hN hstate J L).symm v ∈ rescaledGraphSubspace M J Ω c := by
  let W := stateGraphUnitary θ Ω ξ hM hN hstate J L
  have hc : IsClosed {v : TomitaGraphHilbert K | W.symm v ∈ rescaledGraphSubspace M J Ω c} :=
    (Submodule.isClosed_topologicalClosure _).preimage W.symm.continuous
  apply closure_minimal (s := Set.range (rescaledGraphMap N L ξ c)) ?_ hc hv
  rintro _ ⟨a, rfl⟩
  have he := stateGraphUnitary_vector θ Ω ξ hM hN hstate J L c (θ.symm a)
  rw [θ.apply_symm_apply] at he
  change W (rescaledGraphVector J Ω c (θ.symm a).val) = rescaledGraphVector L ξ c a.val at he
  change W.symm (rescaledGraphVector L ξ c a.val) ∈ rescaledGraphSubspace M J Ω c
  rw [← he, W.symm_apply_apply]
  exact rescaledGraphVector_mem M J Ω c (θ.symm a)

theorem stateGraphProjection_transport (c : ℝ) (v : TomitaGraphHilbert H) :
    rescaledGraphProjection N L ξ c (stateGraphUnitary θ Ω ξ hM hN hstate J L v) =
      stateGraphUnitary θ Ω ξ hM hN hstate J L (rescaledGraphProjection M J Ω c v) := by
  let W := stateGraphUnitary θ Ω ξ hM hN hstate J L
  apply (rescaledGraphSubspace N L ξ c).eq_starProjection_of_mem_of_inner_eq_zero
  · exact stateGraphUnitary_mem θ Ω ξ hM hN hstate J L c
      ((rescaledGraphSubspace M J Ω c).starProjection_apply_mem v)
  · intro w hw
    change inner ℂ (W v - W (rescaledGraphProjection M J Ω c v)) w = 0
    rw [← map_sub]
    conv_lhs => arg 3; rw [← W.apply_symm_apply w]
    rw [W.inner_map_map]
    exact (rescaledGraphSubspace M J Ω c).starProjection_inner_eq_zero v _
      (stateGraphUnitary_symm_mem θ Ω ξ hM hN hstate J L c hw)

end

end KadisonKastler

end OAI
