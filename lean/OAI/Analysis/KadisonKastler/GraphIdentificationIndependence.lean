import OAI.Analysis.KadisonKastler.RescaledGraphAction
import OAI.Analysis.KadisonKastler.GraphResolventCompression

namespace OAI

/-! # Independence of the auxiliary graph identification

Changing the antiunitary used to identify the second graph coordinate
conjugates the graph projection by a diagonal unitary whose first entry
is the identity. Its first compression is therefore unchanged.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

def graphIdentificationUnitary (J K : H ≃ₗᵢ⋆[ℂ] H) :
    unitary (TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) :=
  graphDiagonalUnitary 1 (Unitary.linearIsometryEquiv.symm (J.symm.trans K))

theorem graphIdentificationUnitary_vector (J K : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ)
    (a : H →L[ℂ] H) :
    (graphIdentificationUnitary J K : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H)
      (rescaledGraphVector J Ω c a) = rescaledGraphVector K Ω c a := by
  apply PiLp.ext
  intro i
  fin_cases i
  · change (graphDiagonalUnitary 1 (Unitary.linearIsometryEquiv.symm (J.symm.trans K)) :
      TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) (rescaledGraphVector J Ω c a) 0 = _
    rw [graphDiagonalUnitary_apply_zero]
    rfl
  · change (graphDiagonalUnitary 1 (Unitary.linearIsometryEquiv.symm (J.symm.trans K)) :
      TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) (rescaledGraphVector J Ω c a) 1 = _
    rw [graphDiagonalUnitary_apply_one]
    change K (J.symm (c • J (star a Ω))) = c • K (star a Ω)
    simp only [← Complex.coe_smul]
    rw [J.symm.map_smulₛₗ, Complex.conj_ofReal, J.symm_apply_apply, K.map_smulₛₗ,
      Complex.conj_ofReal]

private theorem graphIdentificationUnitary_mem (J K : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ)
    {v : TomitaGraphHilbert H} (hv : v ∈ rescaledGraphSubspace M J Ω c) :
    (graphIdentificationUnitary J K : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) v ∈
      rescaledGraphSubspace M K Ω c := by
  have hc : IsClosed {v : TomitaGraphHilbert H |
      (graphIdentificationUnitary J K : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) v ∈
        rescaledGraphSubspace M K Ω c} :=
    (Submodule.isClosed_topologicalClosure _).preimage (map_continuous _)
  apply closure_minimal (s := Set.range (rescaledGraphMap M J Ω c)) ?_ hc hv
  rintro _ ⟨a, rfl⟩
  change (graphIdentificationUnitary J K : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H)
    (rescaledGraphVector J Ω c a.val) ∈ rescaledGraphSubspace M K Ω c
  rw [graphIdentificationUnitary_vector]
  exact rescaledGraphVector_mem M K Ω c a

private theorem graphIdentificationUnitary_star_mem (J K : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ)
    {v : TomitaGraphHilbert H} (hv : v ∈ rescaledGraphSubspace M K Ω c) :
    (star (graphIdentificationUnitary J K) : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) v ∈
      rescaledGraphSubspace M J Ω c := by
  let U := graphIdentificationUnitary J K
  have hc : IsClosed {v : TomitaGraphHilbert H |
      (star U : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) v ∈
        rescaledGraphSubspace M J Ω c} :=
    (Submodule.isClosed_topologicalClosure _).preimage (map_continuous _)
  apply closure_minimal (s := Set.range (rescaledGraphMap M K Ω c)) ?_ hc hv
  rintro _ ⟨a, rfl⟩
  change (star U : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H)
    (rescaledGraphVector K Ω c a.val) ∈ rescaledGraphSubspace M J Ω c
  rw [← graphIdentificationUnitary_vector J K]
  have he (w : TomitaGraphHilbert H) :
      (star U : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) (U.val w) = w :=
    congrArg (fun T : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H => T w) U.property.1
  rw [he]
  exact rescaledGraphVector_mem M J Ω c a

theorem graphProjection_identification_transport (J K : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ)
    (v : TomitaGraphHilbert H) :
    rescaledGraphProjection M K Ω c
      ((graphIdentificationUnitary J K : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) v) =
      (graphIdentificationUnitary J K : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H)
        (rescaledGraphProjection M J Ω c v) := by
  let U := graphIdentificationUnitary J K
  apply (rescaledGraphSubspace M K Ω c).eq_starProjection_of_mem_of_inner_eq_zero
  · exact graphIdentificationUnitary_mem J K Ω c
      ((rescaledGraphSubspace M J Ω c).starProjection_apply_mem v)
  · intro w hw
    change inner ℂ (U.val v - U.val (rescaledGraphProjection M J Ω c v)) w = 0
    rw [← map_sub, ← ContinuousLinearMap.adjoint_inner_right]
    exact (rescaledGraphSubspace M J Ω c).starProjection_inner_eq_zero v _
      (graphIdentificationUnitary_star_mem J K Ω c hw)

/-- The graph resolvent does not depend on the auxiliary antiunitary. -/
theorem graphResolvent_identification_independent (J K : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ) :
    graphResolvent M J Ω c = graphResolvent M K Ω c := by
  ext x
  have ht := graphProjection_identification_transport (M := M) J K Ω c (Generator.tupleSingle 0 x)
  have hsingle :
      (graphIdentificationUnitary J K : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H)
        (Generator.tupleSingle 0 x) = Generator.tupleSingle 0 x := by
    apply PiLp.ext
    intro i
    fin_cases i
    · change (graphDiagonalUnitary 1 (Unitary.linearIsometryEquiv.symm (J.symm.trans K)) : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) _ 0 = _
      rw [graphDiagonalUnitary_apply_zero]
      rfl
    · change (graphDiagonalUnitary 1 (Unitary.linearIsometryEquiv.symm (J.symm.trans K)) : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) _ 1 = _
      rw [graphDiagonalUnitary_apply_one]
      simp [Generator.tupleSingle_apply]
  rw [hsingle] at ht
  have h0 := congrArg (fun v : TomitaGraphHilbert H => v 0) ht
  change graphResolvent M K Ω c x =
    (graphDiagonalUnitary 1 (Unitary.linearIsometryEquiv.symm (J.symm.trans K)) : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H)
      (rescaledGraphProjection M J Ω c (Generator.tupleSingle 0 x)) 0 at h0
  rw [graphDiagonalUnitary_apply_zero] at h0
  exact h0.symm

end

end KadisonKastler

end OAI
