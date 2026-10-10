import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Algebra.Tower

namespace OAI

universe u

namespace ArExplicit

variable (R : Type u) [Ring R]
variable (M N : Type u) [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

def FactorsThroughFiniteFree (f : M →ₗ[R] N) : Prop :=
  ∃ (P : Type u) (_ : AddCommGroup P) (_ : Module R P)
    (_ : Module.Free R P) (_ : Module.Finite R P)
    (i : M →ₗ[R] P) (p : P →ₗ[R] N), p.comp i = f

def FactorsThroughFiniteProjective (f : M →ₗ[R] N) : Prop :=
  ∃ (P : Type u) (_ : AddCommGroup P) (_ : Module R P)
    (_ : Module.Projective R P) (_ : Module.Finite R P)
    (i : M →ₗ[R] P) (p : P →ₗ[R] N), p.comp i = f

variable {R M N}

theorem factorsThroughFiniteFree_iff_projective (f : M →ₗ[R] N) :
    FactorsThroughFiniteFree R M N f ↔ FactorsThroughFiniteProjective R M N f := by
  constructor
  · rintro ⟨P, hP, hRP, hfree, hfinite, i, p, h⟩
    exact ⟨P, hP, hRP, inferInstance, hfinite, i, p, h⟩
  · rintro ⟨P, hP, hRP, hprojective, hfinite, i, p, h⟩
    obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R P
    obtain ⟨s, hs⟩ := Module.projective_lifting_property π (LinearMap.id : P →ₗ[R] P) hπ
    refine ⟨Fin n → R, inferInstance, inferInstance, inferInstance, inferInstance,
      s.comp i, p.comp π, ?_⟩
    ext x
    calc
      p (π (s (i x))) = p (i x) := congrArg p (DFunLike.congr_fun hs (i x))
      _ = f x := DFunLike.congr_fun h x

theorem factorsThroughFiniteFree_zero :
    FactorsThroughFiniteFree R M N (0 : M →ₗ[R] N) := by
  exact ⟨R, inferInstance, inferInstance, inferInstance, inferInstance, 0, 0, rfl⟩

theorem FactorsThroughFiniteFree.add {f g : M →ₗ[R] N}
    (hf : FactorsThroughFiniteFree R M N f) (hg : FactorsThroughFiniteFree R M N g) :
    FactorsThroughFiniteFree R M N (f + g) := by
  rcases hf with ⟨P, hP, hRP, hfreeP, hfiniteP, i, p, rfl⟩
  rcases hg with ⟨Q, hQ, hRQ, hfreeQ, hfiniteQ, j, q, rfl⟩
  refine ⟨P × Q, inferInstance, inferInstance, inferInstance, inferInstance,
    i.prod j, p.coprod q, ?_⟩
  ext x
  rfl

theorem FactorsThroughFiniteFree.neg {f : M →ₗ[R] N}
    (hf : FactorsThroughFiniteFree R M N f) :
    FactorsThroughFiniteFree R M N (-f) := by
  rcases hf with ⟨P, hP, hRP, hfreeP, hfiniteP, i, p, rfl⟩
  refine ⟨P, hP, hRP, hfreeP, hfiniteP, i, -p, ?_⟩
  ext x
  rfl

variable {L P : Type u} [AddCommGroup L] [Module R L] [AddCommGroup P] [Module R P]

theorem FactorsThroughFiniteFree.postcomp {f : M →ₗ[R] N}
    (hf : FactorsThroughFiniteFree R M N f) (g : N →ₗ[R] P) :
    FactorsThroughFiniteFree R M P (g.comp f) := by
  rcases hf with ⟨Q, hQ, hRQ, hfreeQ, hfiniteQ, i, p, rfl⟩
  exact ⟨Q, hQ, hRQ, hfreeQ, hfiniteQ, i, g.comp p, LinearMap.comp_assoc ..⟩

theorem FactorsThroughFiniteFree.precomp {f : M →ₗ[R] N}
    (hf : FactorsThroughFiniteFree R M N f) (g : L →ₗ[R] M) :
    FactorsThroughFiniteFree R L N (f.comp g) := by
  rcases hf with ⟨Q, hQ, hRQ, hfreeQ, hfiniteQ, i, p, rfl⟩
  exact ⟨Q, hQ, hRQ, hfreeQ, hfiniteQ, i.comp g, p, (LinearMap.comp_assoc ..).symm⟩

variable (R M N)

def projectiveMaps : AddSubgroup (M →ₗ[R] N) where
  carrier := FactorsThroughFiniteFree R M N
  zero_mem' := factorsThroughFiniteFree_zero
  add_mem' := FactorsThroughFiniteFree.add
  neg_mem' := FactorsThroughFiniteFree.neg

abbrev StableHom := (M →ₗ[R] N) ⧸ projectiveMaps R M N

namespace StableHom

def classOf : (M →ₗ[R] N) →+ StableHom R M N :=
  QuotientAddGroup.mk' (projectiveMaps R M N)

variable {R M N}

theorem classOf_surjective : Function.Surjective (classOf R M N) :=
  QuotientAddGroup.mk'_surjective _

@[simp]
theorem classOf_eq_zero_iff (f : M →ₗ[R] N) :
    classOf R M N f = 0 ↔ FactorsThroughFiniteFree R M N f :=
  QuotientAddGroup.eq_zero_iff f

theorem classOf_eq_zero_iff_projective (f : M →ₗ[R] N) :
    classOf R M N f = 0 ↔ FactorsThroughFiniteProjective R M N f := by
  rw [classOf_eq_zero_iff, factorsThroughFiniteFree_iff_projective]

@[simp]
theorem classOf_eq_iff (f g : M →ₗ[R] N) :
    classOf R M N f = classOf R M N g ↔ FactorsThroughFiniteFree R M N (f - g) :=
  QuotientAddGroup.eq_iff_sub_mem

theorem identity_eq_zero_iff [Module.Finite R M] :
    classOf R M M LinearMap.id = 0 ↔ Module.Projective R M := by
  rw [classOf_eq_zero_iff_projective]
  constructor
  · rintro ⟨P, hP, hRP, hprojective, hfinite, i, p, h⟩
    exact Module.Projective.of_split i p h
  · intro h
    exact ⟨M, inferInstance, inferInstance, h, inferInstance,
      LinearMap.id, LinearMap.id, rfl⟩

def postcomp (g : N →ₗ[R] P) : StableHom R M N →+ StableHom R M P :=
  QuotientAddGroup.map (projectiveMaps R M N) (projectiveMaps R M P)
    { toFun := fun f => g.comp f
      map_zero' := LinearMap.comp_zero g
      map_add' := by intros; ext x; simp }
    (fun _ hf => hf.postcomp g)

def precomp (g : L →ₗ[R] M) : StableHom R M N →+ StableHom R L N :=
  QuotientAddGroup.map (projectiveMaps R M N) (projectiveMaps R L N)
    { toFun := fun f => f.comp g
      map_zero' := LinearMap.zero_comp g
      map_add' := by intros; ext x; simp }
    (fun _ hf => hf.precomp g)

@[simp]
theorem postcomp_classOf (g : N →ₗ[R] P) (f : M →ₗ[R] N) :
    postcomp g (classOf R M N f) = classOf R M P (g.comp f) := by
  exact QuotientAddGroup.map_mk' _ _ _ _ _

@[simp]
theorem precomp_classOf (g : L →ₗ[R] M) (f : M →ₗ[R] N) :
    precomp g (classOf R M N f) = classOf R L N (f.comp g) := by
  exact QuotientAddGroup.map_mk' _ _ _ _ _

def postcompHom : (N →ₗ[R] P) →+ (StableHom R M N →+ StableHom R M P) where
  toFun := postcomp
  map_zero' := by
    apply AddMonoidHom.ext
    intro f
    obtain ⟨f, rfl⟩ := classOf_surjective f
    simp
  map_add' := by
    intro g h
    apply AddMonoidHom.ext
    intro f
    obtain ⟨f, rfl⟩ := classOf_surjective f
    simp only [AddMonoidHom.add_apply, postcomp_classOf]
    rw [show (g + h).comp f = g.comp f + h.comp f by ext x; rfl]
    exact map_add (classOf R M P) _ _

def comp : StableHom R N P →+ (StableHom R M N →+ StableHom R M P) :=
  QuotientAddGroup.lift (projectiveMaps R N P) postcompHom (by
    intro g hg
    change postcomp g = 0
    apply AddMonoidHom.ext
    intro f
    obtain ⟨f, rfl⟩ := classOf_surjective f
    exact (classOf_eq_zero_iff (g.comp f)).mpr (hg.precomp f))

@[simp]
theorem comp_classOf (g : N →ₗ[R] P) (f : M →ₗ[R] N) :
    comp (classOf R N P g) (classOf R M N f) = classOf R M P (g.comp f) := by
  change postcomp g (classOf R M N f) = _
  exact postcomp_classOf g f

def identity : StableHom R M M := classOf R M M LinearMap.id

@[simp]
theorem identity_comp (f : StableHom R M N) : comp identity f = f := by
  obtain ⟨f, rfl⟩ := classOf_surjective f
  simp [identity]

@[simp]
theorem comp_identity (f : StableHom R M N) : comp f identity = f := by
  obtain ⟨f, rfl⟩ := classOf_surjective f
  simp [identity]

theorem comp_assoc {Q : Type u} [AddCommGroup Q] [Module R Q]
    (h : StableHom R P Q) (g : StableHom R N P) (f : StableHom R M N) :
    comp h (comp g f) = comp (comp h g) f := by
  obtain ⟨h, rfl⟩ := classOf_surjective h
  obtain ⟨g, rfl⟩ := classOf_surjective g
  obtain ⟨f, rfl⟩ := classOf_surjective f
  simp only [comp_classOf, LinearMap.comp_assoc]

theorem eq_zero_of_projective_source [Module.Finite R M] [Module.Projective R M]
    (f : StableHom R M N) : f = 0 := by
  obtain ⟨f, rfl⟩ := classOf_surjective f
  apply (classOf_eq_zero_iff_projective f).mpr
  exact ⟨M, inferInstance, inferInstance, inferInstance, inferInstance,
    LinearMap.id, f, LinearMap.comp_id _⟩

theorem eq_zero_of_projective_target [Module.Finite R N] [Module.Projective R N]
    (f : StableHom R M N) : f = 0 := by
  obtain ⟨f, rfl⟩ := classOf_surjective f
  apply (classOf_eq_zero_iff_projective f).mpr
  exact ⟨N, inferInstance, inferInstance, inferInstance, inferInstance,
    f, LinearMap.id, LinearMap.id_comp _⟩

end StableHom

section CentralScalars

variable {R M N}
variable (k : Type u) [CommRing k] [Algebra k R]
variable [Module k N] [IsScalarTower k R N]

theorem FactorsThroughFiniteFree.smul {f : M →ₗ[R] N}
    (hf : FactorsThroughFiniteFree R M N f) (a : k) :
    FactorsThroughFiniteFree R M N (a • f) := by
  rcases hf with ⟨Q, hQ, hRQ, hfreeQ, hfiniteQ, i, p, rfl⟩
  refine ⟨Q, hQ, hRQ, hfreeQ, hfiniteQ, i, a • p, ?_⟩
  ext x
  rfl

def projectiveMapsSubmodule : Submodule k (M →ₗ[R] N) where
  __ := projectiveMaps R M N
  smul_mem' := fun a _ hf => hf.smul k a

instance stableHomModule : Module k (StableHom R M N) :=
  inferInstanceAs (Module k ((M →ₗ[R] N) ⧸ projectiveMapsSubmodule k))

namespace StableHom

def classOfLinear : (M →ₗ[R] N) →ₗ[k] StableHom R M N :=
  (projectiveMapsSubmodule k).mkQ

@[simp]
theorem classOfLinear_apply (f : M →ₗ[R] N) :
    classOfLinear k f = classOf R M N f := rfl

@[simp]
theorem classOf_smul (a : k) (f : M →ₗ[R] N) :
    classOf R M N (a • f) = a • classOf R M N f :=
  (classOfLinear k).map_smul a f

variable [Module k P] [IsScalarTower k R P]

theorem comp_smul (g : StableHom R N P) (a : k) (f : StableHom R M N) :
    comp g (a • f) = a • comp g f := by
  obtain ⟨g, rfl⟩ := classOf_surjective g
  obtain ⟨f, rfl⟩ := classOf_surjective f
  rw [← classOf_smul k a f, comp_classOf, LinearMap.comp_smul,
    classOf_smul, comp_classOf]

omit [Module k N] [IsScalarTower k R N] in
theorem smul_comp (a : k) (g : StableHom R N P) (f : StableHom R M N) :
    comp (a • g) f = a • comp g f := by
  obtain ⟨g, rfl⟩ := classOf_surjective g
  obtain ⟨f, rfl⟩ := classOf_surjective f
  rw [← classOf_smul k a g, comp_classOf, LinearMap.smul_comp,
    classOf_smul, comp_classOf]

def postcompLinear (g : StableHom R N P) :
    StableHom R M N →ₗ[k] StableHom R M P where
  toFun := comp g
  map_add' := map_add (comp g)
  map_smul' := comp_smul k g

def compLinear :
    StableHom R N P →ₗ[k] (StableHom R M N →ₗ[k] StableHom R M P) where
  toFun := postcompLinear k
  map_add' := by
    intro g h
    apply LinearMap.ext
    intro f
    change comp (g + h) f = comp g f + comp h f
    exact DFunLike.congr_fun (map_add comp g h) f
  map_smul' := by
    intro a g
    apply LinearMap.ext
    intro f
    exact smul_comp k a g f

@[simp]
theorem compLinear_apply (g : StableHom R N P) (f : StableHom R M N) :
    compLinear k g f = comp g f := rfl

end StableHom

end CentralScalars

end ArExplicit

end OAI
