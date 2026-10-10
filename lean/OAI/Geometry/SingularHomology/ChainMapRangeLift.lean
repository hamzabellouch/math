import OAI.Geometry.SingularHomology.HomologyCycle

namespace OAI

noncomputable section

open CategoryTheory

namespace Problem340.ChainMapRangeLift

variable {R : Type*} [Ring R]

section Linear

variable {M N P : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [Module R M] [Module R N] [Module R P]

def linearLift (i : M →ₗ[R] N) (hi : Function.Injective i)
    (f : P →ₗ[R] N) (hf : ∀ x, f x ∈ LinearMap.range i) : P →ₗ[R] M :=
  (LinearEquiv.ofInjective i hi).symm.toLinearMap.comp
    (f.codRestrict (LinearMap.range i) hf)

@[simp] theorem linearLift_apply (i : M →ₗ[R] N) (hi : Function.Injective i)
    (f : P →ₗ[R] N) (hf : ∀ x, f x ∈ LinearMap.range i) (x : P) :
    i (linearLift i hi f hf x) = f x := by
  exact congrArg Subtype.val
    ((LinearEquiv.ofInjective i hi).apply_symm_apply ⟨f x, hf x⟩)

end Linear

section Complexes

variable {ι : Type*} {c : ComplexShape ι}
  {C D E : HomologicalComplex (ModuleCat R) c}

theorem comm_apply (f : C ⟶ D) (i j : ι) (x : C.X i) :
    (D.d i j).hom ((f.f i).hom x) = (f.f j).hom ((C.d i j).hom x) :=
  congrArg (fun k : C.X i ⟶ D.X j => k.hom x) (f.comm i j)

def liftChainMap (φ : C ⟶ D) (hinj : ∀ n, Function.Injective (φ.f n).hom)
    (f : E ⟶ D) (hf : ∀ n (x : E.X n), (f.f n).hom x ∈ LinearMap.range (φ.f n).hom) :
    E ⟶ C where
  f n := ModuleCat.ofHom (linearLift (φ.f n).hom (hinj n) (f.f n).hom (hf n))
  comm' i j _ := by
    ext x
    apply hinj j
    change (φ.f j).hom ((C.d i j).hom
      (linearLift (φ.f i).hom (hinj i) (f.f i).hom (hf i) x)) =
      (φ.f j).hom (linearLift (φ.f j).hom (hinj j) (f.f j).hom (hf j)
        ((E.d i j).hom x))
    rw [← comm_apply φ i j, linearLift_apply, linearLift_apply, comm_apply f i j]

@[simp] theorem liftChainMap_comp (φ : C ⟶ D)
    (hinj : ∀ n, Function.Injective (φ.f n).hom)
    (f : E ⟶ D) (hf : ∀ n (x : E.X n), (f.f n).hom x ∈ LinearMap.range (φ.f n).hom) :
    liftChainMap φ hinj f hf ≫ φ = f := by
  ext n x
  exact linearLift_apply (φ.f n).hom (hinj n) (f.f n).hom (hf n) x

theorem liftChainMap_eq (φ : C ⟶ D) (hinj : ∀ n, Function.Injective (φ.f n).hom)
    (f : E ⟶ D) (hf : ∀ n (x : E.X n), (f.f n).hom x ∈ LinearMap.range (φ.f n).hom)
    (g : E ⟶ C) (hg : g ≫ φ = f) : liftChainMap φ hinj f hf = g := by
  ext n x
  apply hinj n
  have h := congrArg (fun k : E ⟶ D => (k.f n).hom x) hg
  change (φ.f n).hom ((g.f n).hom x) = (f.f n).hom x at h
  exact (linearLift_apply (φ.f n).hom (hinj n) (f.f n).hom (hf n) x).trans h.symm

def liftChainHomotopy (φ : C ⟶ D) (hinj : ∀ n, Function.Injective (φ.f n).hom)
    (f g : E ⟶ D)
    (hf : ∀ n (x : E.X n), (f.f n).hom x ∈ LinearMap.range (φ.f n).hom)
    (hg : ∀ n (x : E.X n), (g.f n).hom x ∈ LinearMap.range (φ.f n).hom)
    (H : Homotopy f g)
    (hH : ∀ i j (x : E.X i), (H.hom i j).hom x ∈ LinearMap.range (φ.f j).hom) :
    Homotopy (liftChainMap φ hinj f hf) (liftChainMap φ hinj g hg) where
  hom i j := ModuleCat.ofHom (linearLift (φ.f j).hom (hinj j) (H.hom i j).hom (hH i j))
  zero i j hij := by
    ext x
    apply hinj j
    change (φ.f j).hom (linearLift (φ.f j).hom (hinj j)
      (H.hom i j).hom (hH i j) x) = (φ.f j).hom 0
    rw [map_zero, linearLift_apply, H.zero i j hij]
    rfl
  comm i := by
    ext x
    apply hinj i
    have h := congrArg (fun k : E.X i ⟶ D.X i => k.hom x) (H.comm i)
    change (f.f i).hom x =
      (H.hom (c.next i) i).hom ((E.d i (c.next i)).hom x) +
      (D.d (c.prev i) i).hom ((H.hom i (c.prev i)).hom x) + (g.f i).hom x at h
    change (φ.f i).hom (linearLift (φ.f i).hom (hinj i) (f.f i).hom (hf i) x) =
      (φ.f i).hom (linearLift (φ.f i).hom (hinj i)
          (H.hom (c.next i) i).hom (hH (c.next i) i) ((E.d i (c.next i)).hom x) +
        (C.d (c.prev i) i).hom (linearLift (φ.f (c.prev i)).hom (hinj (c.prev i))
          (H.hom i (c.prev i)).hom (hH i (c.prev i)) x) +
        linearLift (φ.f i).hom (hinj i) (g.f i).hom (hg i) x)
    rw [map_add, map_add, linearLift_apply, linearLift_apply, linearLift_apply,
      ← comm_apply φ (c.prev i) i, linearLift_apply]
    exact h

end Complexes

end Problem340.ChainMapRangeLift

end

end OAI
