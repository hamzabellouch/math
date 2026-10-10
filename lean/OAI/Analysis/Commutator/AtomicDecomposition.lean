import Mathlib
import OAI.Analysis.Commutator.FactorCorner
import OAI.Analysis.Commutator.MinimalProjection
import OAI.Analysis.Commutator.OrthogonalLinkSums

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology BigOperators

open Filter

universe u

namespace Kadison.AtomicFactor

open PartialIsometryOrder

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

structure Decomposition (M : VonNeumannAlgebra H) (p : H →L[ℂ] H) where
  I : Type u
  v : I → H →L[ℂ] H
  mem : ∀ i,v i∈M
  initial : ∀ i,star (v i)*v i=p
  cross : ∀ i j,i≠j → star (v i)*v j=0
  source : ∀ i,v i*p=v i
  strong : ∀ x : H,Tendsto (fun s : Finset I => (∑ i∈s,v i*star (v i)) x) atTop (𝓝 x)

theorem exists_decomposition (M : VonNeumannAlgebra H) (hM : FactorCorner.IsFactor M)
    {p : H →L[ℂ] H} (hp : IsMinimalProjection M p) : Nonempty (Decomposition M p) := by
  classical
  obtain ⟨S,hS⟩ := exists_maximal_orthogonalLinks M p 1
  let T : Set (Link M p 1) := {v | v∈S ∧ v.val≠0}
  have hTS : T⊆S := fun _ h => h.1
  have hT : OrthogonalLinks M p 1 T := fun _ hv _ hw hne => hS.1 (hTS hv) (hTS hw) hne
  have hspaces : familySpace M p 1 T=familySpace M p 1 S := by
    apply le_antisymm
    · apply Submodule.topologicalClosure_mono
      apply Submodule.span_mono
      rintro x ⟨v,hv,ξ,rfl⟩
      exact ⟨v,hTS hv,ξ,rfl⟩
    · apply Submodule.topologicalClosure_minimal
      · apply Submodule.span_le.mpr
        rintro x ⟨v,hv,ξ,rfl⟩
        change v.val ξ∈familySpace M p 1 T
        by_cases hz : v.val=0
        · rw [hz]
          exact (familySpace M p 1 T).zero_mem
        · exact familySpace_generator M p 1 T ⟨hv,hz⟩ ξ
      · exact Submodule.isClosed_topologicalClosure _
  have hspan : (familySpace M p 1 T).starProjection=1 := by
    have he : (familySpace M p 1 T).starProjection=(familySpace M p 1 S).starProjection := by
      congr 1
    rw [he]
    exact maximal_family_spans M p 1 hM hp.1 M.one_mem hp.2.1 (IsStarProjection.one _) hp.2.2.1 S hS
  refine ⟨⟨T,fun i => i.val.val,fun i => i.val.mem,?_,?_,?_,?_⟩⟩
  · intro i
    rcases hp.2.2.2 i.val.initial (M.mul_mem (M.star_mem' i.val.mem) i.val.mem)
      i.val.initial_projection i.val.source_le with hz|hz
    · have he := i.val.mul_initial
      rw [hz,mul_zero] at he
      exact (i.property.2 he.symm).elim
    · exact hz
  · intro i j hne
    exact family_cross M p 1 T hT hne
  · intro i
    exact i.val.mul_source hp.2.1
  · intro x
    simpa only [finiteProjection,Link.final,one_apply_eq_self] using
      finiteProjection_tendsto M p 1 T hT (IsStarProjection.one _) hspan x

end Kadison.AtomicFactor

end

end
end

end OAI
