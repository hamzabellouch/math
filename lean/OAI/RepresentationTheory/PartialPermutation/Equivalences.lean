import Mathlib
import OAI.RepresentationTheory.PartialPermutation.Plancherel

namespace OAI

section
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators
open scoped BigOperators MonoidAlgebra Classical

attribute [local instance] Classical.propDecidable
open scoped MonoidAlgebra BigOperators
open scoped BigOperators

namespace PartialPermutation
noncomputable section
variable {G K V W : Type*} [Group G] [Group K]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def subrepresentationCompEquiv (ρ : Representation ℂ G V) (e : K ≃* G) :
    Subrepresentation (ρ.comp e.toMonoidHom) ≃o Subrepresentation ρ where
  toFun S :=
    { toSubmodule := S.toSubmodule
      apply_mem_toSubmodule := by
        intro g v hv
        simpa using S.apply_mem_toSubmodule (e.symm g) hv }
  invFun S :=
    { toSubmodule := S.toSubmodule
      apply_mem_toSubmodule := fun g v hv => S.apply_mem_toSubmodule (e g) hv }
  left_inv S := by ext; rfl
  right_inv S := by ext; rfl
  map_rel_iff' := Iff.rfl

instance irreducible_comp_mulEquiv (ρ : Representation ℂ G V)
    [Representation.IsIrreducible ρ] (e : K ≃* G) :
    Representation.IsIrreducible (ρ.comp e.toMonoidHom) :=
  (subrepresentationCompEquiv ρ e).isSimpleOrder_iff.mpr inferInstance

def representationEquivComp {ρ σ : Representation ℂ G V}
    (a : Representation.Equiv ρ σ) (e : K →* G) :
    Representation.Equiv (ρ.comp e) (σ.comp e) :=
  Representation.Equiv.mk a.toLinearEquiv (fun g => a.isIntertwining' (e g))

def representationEquivCompGeneral {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (a : Representation.Equiv ρ σ) (e : K →* G) :
    Representation.Equiv (ρ.comp e) (σ.comp e) :=
  Representation.Equiv.mk a.toLinearEquiv (fun g => a.isIntertwining' (e g))

variable [Fintype G] [Fintype K]

def irreducibleIndexMap (e : G ≃* K) (c : IrreducibleIndex G) : IrreducibleIndex K :=
  (irreducibleRep_complete ((irreducibleRep c).comp e.symm.toMonoidHom)).choose

lemma irreducibleIndexMap_spec (e : G ≃* K) (c : IrreducibleIndex G) :
    Nonempty (Representation.Equiv (irreducibleRep (irreducibleIndexMap e c))
      ((irreducibleRep c).comp e.symm.toMonoidHom)) :=
  (irreducibleRep_complete ((irreducibleRep c).comp e.symm.toMonoidHom)).choose_spec.1

lemma irreducibleIndexMap_inverse (e : G ≃* K) (c : IrreducibleIndex G) :
    irreducibleIndexMap e.symm (irreducibleIndexMap e c) = c := by
  obtain ⟨a⟩ := irreducibleIndexMap_spec e c
  obtain ⟨b⟩ := irreducibleIndexMap_spec e.symm (irreducibleIndexMap e c)
  have h : Nonempty (Representation.Equiv
      (irreducibleRep (irreducibleIndexMap e.symm (irreducibleIndexMap e c)))
      (irreducibleRep c)) := by
    refine ⟨Representation.Equiv.mk (b.toLinearEquiv.trans a.toLinearEquiv) ?_⟩
    intro g
    apply LinearMap.ext
    intro x
    change a (b (irreducibleRep _ g x)) = irreducibleRep c g (a (b x))
    calc
      _ = a (irreducibleRep (irreducibleIndexMap e c) (e g) (b x)) :=
        congrArg a (congrArg (fun L : _ →ₗ[ℂ] _ => L x) (b.isIntertwining' g))
      _ = _ := by
        have ha := congrArg (fun L : _ →ₗ[ℂ] _ => L (b x)) (a.isIntertwining' (e g))
        change a (irreducibleRep (irreducibleIndexMap e c) (e g) (b x)) =
          irreducibleRep c (e.symm (e g)) (a (b x)) at ha
        simpa only [MulEquiv.symm_apply_apply] using ha
  exact (componentRep_equiv_iff (regularRep G) _ _).mp h

def irreducibleIndexEquiv (e : G ≃* K) : IrreducibleIndex G ≃ IrreducibleIndex K where
  toFun := irreducibleIndexMap e
  invFun := irreducibleIndexMap e.symm
  left_inv := irreducibleIndexMap_inverse e
  right_inv := irreducibleIndexMap_inverse e.symm

lemma irreducibleDegree_map (e : G ≃* K) (c : IrreducibleIndex G) :
    irreducibleDegree (irreducibleIndexMap e c) = irreducibleDegree c := by
  obtain ⟨a⟩ := irreducibleIndexMap_spec e c
  exact a.toLinearEquiv.finrank_eq

lemma inverseDegreeSum_equiv (e : G ≃* K) (u : ℝ) :
    inverseDegreeSum G u = inverseDegreeSum K u := by
  apply Fintype.sum_equiv (irreducibleIndexEquiv e)
  intro c
  change (irreducibleDegree c : ℝ)^(-u) = (irreducibleDegree (irreducibleIndexMap e c) : ℝ)^(-u)
  rw [irreducibleDegree_map]

end
end PartialPermutation

end

end OAI
