import OAI.RepresentationTheory.RestrictedTilting.NormConverse
import OAI.RepresentationTheory.RestrictedTilting.NormFree

namespace OAI

namespace FiberFunctorProof
open CategoryTheory Representation
universe u
variable {k : Type u} [Field k] {G : Type u} [Group G] [Fintype G]
variable {V : Type u} [AddCommGroup V] [Module k V]

 

theorem norm_bijective_of_projective (ρ : Representation k G V)
    (hρ : Projective (Rep.of ρ)) : Function.Bijective (coinvariantNorm ρ) := by
  let e : Rep.free k G V ⟶ Rep.of ρ := Rep.ofHom (Representation.freeLift ρ id)
  have he : Function.Surjective e.hom := by
    intro v
    refine ⟨Finsupp.single v (MonoidAlgebra.single 1 1), ?_⟩
    simp [e]
  let : Epi e := (Rep.epi_iff_surjective e).2 he
  obtain ⟨s,hs⟩ := hρ.factors (𝟙 (Rep.of ρ)) e
  apply norm_bijective_of_retract s.hom e.hom
  · exact congrArg Rep.Hom.hom hs
  · exact free_norm_bijective V

 

theorem norm_projectivity : NormProjectivityTheorem.{u} := by
  intro k _ _ p _ _
  constructor
  · intro G _ _ hG V _ _ _ ρ
    constructor
    · exact norm_bijective_of_projective ρ
    · intro h
      exact projective_of_normSurjective hG ρ ((coinvariantNorm_surjective_iff ρ).1 h.2)
  · intro G _ _ V _ _ _ ρ
    exact norm_bijective_of_projective ρ
end FiberFunctorProof

end OAI
