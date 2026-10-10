import Mathlib
import OAI.Analysis.Commutator.ProjectionWeighted
import OAI.Analysis.Commutator.SelfAdjointSpectral
import OAI.Analysis.Commutator.VonNeumannCStar

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder BigOperators

namespace Kadison.SpectralPartition

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_spectral_step (M : VonNeumannAlgebra H) (T : H →L[ℂ] H)
    (hTM : T∈M) (hT : IsSelfAdjoint T) {ε : ℝ} (hε : 0<ε) :
    ∃ (J : Type) (_ : Fintype J) (p : J → H →L[ℂ] H) (c : J → ℝ),
      (∀ j,p j∈M ∧ IsStarProjection (p j)) ∧
      (∀ j k,j≠k → p j*p k=0) ∧ (∑ j,p j)=1 ∧
      ‖T-∑ j,c j • p j‖<ε := by
  classical
  obtain ⟨n,p,c,hp,hc,he⟩ := Polar.exists_selfadjoint_spectral_sum M hTM hT hε
  obtain ⟨J,hJ,e,d,hproj,horth,hsum,heq,hcomm⟩ := exists_weighted_partition n p c
    (fun i => (hp i).2) hc
  let : Fintype J := hJ
  refine ⟨J,hJ,e,d,?_,horth,hsum,?_⟩
  · intro j
    refine ⟨?_,hproj j⟩
    change e j∈M.toStarSubalgebra.carrier
    rw [←M.centralizer_centralizer']
    intro a ha
    exact (hcomm a (fun i => (ha (p i) (hp i).1).symm) j).eq
  · rwa [←heq]

theorem exists_spectral_step_subtype (M : VonNeumannAlgebra H) (T : M)
    (hT : IsSelfAdjoint T) {ε : ℝ} (hε : 0<ε) :
    ∃ (J : Type) (_ : Fintype J) (p : J → M) (c : J → ℝ),
      (∀ j,IsStarProjection (p j)) ∧
      (∀ j k,j≠k → p j*p k=0) ∧ (∑ j,p j)=1 ∧
      ‖T-∑ j,(c j:ℂ) • p j‖<ε := by
  classical
  obtain ⟨J,hJ,p,c,hp,ho,hs,he⟩ := exists_spectral_step M T T.property
    (hT.map M.toStarSubalgebra.subtype) hε
  let : Fintype J := hJ
  let q : J → M := fun j => ⟨p j,(hp j).1⟩
  refine ⟨J,hJ,q,c,?_,?_,?_,?_⟩
  · intro j
    constructor
    · exact Subtype.ext (hp j).2.isIdempotentElem.eq
    · exact Subtype.ext (hp j).2.isSelfAdjoint.star_eq
  · intro j k hjk
    exact Subtype.ext (ho j k hjk)
  · apply Subtype.ext
    change M.toStarSubalgebra.subtype (∑ j,q j)=M.toStarSubalgebra.subtype 1
    rw [map_sum,map_one]
    exact hs
  · change ‖(T : H →L[ℂ] H)-((∑ j,(c j:ℂ) • q j : M) : H →L[ℂ] H)‖<ε
    change ‖(T : H →L[ℂ] H)-M.toStarSubalgebra.subtype (∑ j,(c j:ℂ) • q j)‖<ε
    simp only [map_sum,Complex.coe_smul]
    exact he

end Kadison.SpectralPartition

end

end
end

end OAI
