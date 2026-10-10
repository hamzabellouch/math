import OAI.RepresentationTheory.FiniteUnitary.Coefficients

namespace OAI

namespace CubeShuffle.UnitaryFinite
open scoped BigOperators Classical

variable {α ι : Type*} [Fintype α] [Fintype ι]

def tupleAction : Equiv.Perm α →* Equiv.Perm (ι ↪ α) where
  toFun p :=
    { toFun := fun e => e.trans p.toEmbedding
      invFun := fun e => e.trans p.symm.toEmbedding
      left_inv := fun e => by ext i; exact p.symm_apply_apply (e i)
      right_inv := fun e => by ext i; exact p.apply_symm_apply (e i) }
  map_one' := by ext e i; rfl
  map_mul' p q := by ext e i; rfl

omit [Fintype α] [Fintype ι] in
@[simp] lemma tupleAction_apply (p : Equiv.Perm α) (e : ι ↪ α) (i : ι) :
    tupleAction p e i=p (e i) := rfl

omit [Fintype α] in
lemma tupleAction_transitive (e f : ι ↪ α) : ∃ p, tupleAction p e=f := by
  obtain ⟨p,hp⟩ := Equiv.Perm.exists_extending_pair e f e.injective f.injective
  exact ⟨p,Function.Embedding.ext hp⟩

omit [Fintype α] in
lemma tupleAction_fixed_iff [DecidableEq α] (e : ι ↪ α) (p : Equiv.Perm α) :
    tupleAction p e=e ↔ ∀ x ∈ Finset.univ.image e, p x=x := by
  constructor
  · intro h x hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    exact congrArg (fun f : ι ↪ α => f i) h
  · intro h
    ext i
    exact h (e i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)

end CubeShuffle.UnitaryFinite
namespace CubeShuffle.UnitaryFinite
open scoped BigOperators Classical

lemma irreducible_of_equiv {G V W : Type*} [Group G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (e : Representation.Equiv ρ σ) [Representation.IsIrreducible ρ] :
    Representation.IsIrreducible σ := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule]
  have hi := (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp inferInstance
  let f : ρ.asModule →ₗ[MonoidAlgebra ℂ G] σ.asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule ρ σ e.toIntertwiningMap
  have hf : Function.Bijective f := e.toLinearEquiv.bijective
  exact (f.isSimpleModule_iff_of_bijective hf).mp hi

end CubeShuffle.UnitaryFinite

end OAI
