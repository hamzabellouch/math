import OAI.RepresentationTheory.RestrictedTilting.RelativeTrace
import OAI.RepresentationTheory.RestrictedTilting.NormFree
import OAI.RepresentationTheory.RestrictedTilting.ProjectiveFactor
import OAI.RepresentationTheory.RestrictedTilting.ProjectiveRegular

namespace OAI

namespace FiberFunctorProof
open CategoryTheory Representation
universe u
variable {k : Type u} [Field k] {G : Type u} [Group G] [Fintype G]

 

lemma free_relativeTrace (I : Type u) :
    relativeTrace (Representation.free k G I) (Representation.free k G I)
      (freeNormRepresentative I) = LinearMap.id := by
  classical
  apply LinearMap.ext
  intro x
  apply Finsupp.ext
  intro i
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro g
  simp only [relativeTrace_apply, Finsupp.finsetSum_apply,
    free_action_apply, freeNormRepresentative_apply]
  simp [Representation.coeff_ofMulAction]

 
noncomputable def finiteIntertwiner {V W : FDRep k G} (f : Representation.IntertwiningMap V.ρ W.ρ) : V ⟶ W :=
  (FDRep.forget₂HomLinearEquiv V W) (Rep.ofHom f)

omit [Fintype G] in
@[simp] lemma finiteIntertwiner_hom {V W : FDRep k G} (f : Representation.IntertwiningMap V.ρ W.ρ) :
    (finiteIntertwiner f).hom.hom.hom = f.toLinearMap := rfl

omit [Fintype G] in
lemma finiteIntertwiner_epi {V W : FDRep k G} (f : Representation.IntertwiningMap V.ρ W.ρ)
    (hf : Function.Surjective f) : Epi (finiteIntertwiner f) := by
  let F := forget₂ (FDRep k G) (Rep k G)
  have : Epi (F.map (finiteIntertwiner f)) := (Rep.epi_iff_surjective _).2 hf
  exact F.epi_of_epi_map this

 

lemma fdrep_free_projective (I : Type u) [Finite I] :
    Projective (FDRep.of (Representation.free k G I)) := by
  apply (forget₂ (FDRep k G) (Rep k G)).projective_of_map_projective
  exact (Rep.toModuleMonoidAlgebra (k := k) (G := G)).projective_of_map_projective
    (P := Rep.of (Representation.free k G I))
    (ModuleCat.projective_of_free (Representation.freeAsModuleBasis k G I))

 
noncomputable def finiteFreeCover (V : FDRep k G) :
    FDRep.of (Representation.free k G (ULift.{u} (Fin (Module.finrank k V)))) ⟶ V :=
  finiteIntertwiner (Representation.freeLift V.ρ
    (fun i : ULift.{u} (Fin (Module.finrank k V)) => Module.finBasis k V i.down))

lemma finiteFreeCover_epi (V : FDRep k G) : Epi (finiteFreeCover V) := by
  classical
  apply finiteIntertwiner_epi
  intro v
  refine ⟨∑ i : Fin (Module.finrank k V),
    Finsupp.single (ULift.up i) (MonoidAlgebra.single 1 ((Module.finBasis k V).repr v i)), ?_⟩
  change (Representation.freeLift V.ρ (fun i : ULift.{u} (Fin (Module.finrank k V)) =>
    Module.finBasis k V i.down)).toLinearMap _ = v
  rw [map_sum]
  simp only [IntertwiningMap.toLinearMap_apply, Representation.freeLift_single_single,
    map_one, Module.End.one_apply]
  exact (Module.finBasis k V).sum_repr v

end FiberFunctorProof

end OAI
