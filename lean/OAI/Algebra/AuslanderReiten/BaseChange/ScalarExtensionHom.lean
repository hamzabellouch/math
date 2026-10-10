import OAI.Algebra.AuslanderReiten.BaseChange.ScalarExtensionProjective

namespace OAI

noncomputable section
open scoped TensorProduct
namespace ArExplicit
universe u v w
variable (k : Type u) [Field k] (E : Type v) [Field E] [Algebra k E]
  (R : Type w) [Ring R] [Algebra k R]
  {M N L : Type w}
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
  [AddCommGroup N] [Module R N] [Module k N] [IsScalarTower k R N]
  [AddCommGroup L] [Module R L] [Module k L] [IsScalarTower k R L]

attribute [local instance] scalarExtensionModule

def scalarExtensionHomLinear : (M →ₗ[R] N) →ₗ[k]
    ((E ⊗[k] M) →ₗ[E ⊗[k] R] (E ⊗[k] N)) where
  toFun := scalarExtensionMap k E R
  map_add' f g := by
    ext x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul e m => simp [TensorProduct.tmul_add]
  map_smul' a f := by
    ext x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul e m => simp [TensorProduct.tmul_smul]

def scalarExtensionHom : E ⊗[k] (M →ₗ[R] N) →ₗ[E]
    ((E ⊗[k] M) →ₗ[E ⊗[k] R] (E ⊗[k] N)) :=
  (scalarExtensionHomLinear k E R).liftBaseChange E

@[simp]
theorem scalarExtensionHom_tmul (e : E) (f : M →ₗ[R] N) :
    scalarExtensionHom k E R (e ⊗ₜ[k] f) = e • scalarExtensionMap k E R f := rfl

def scalarExtensionHomCoordinates (n : ℕ) :
    ((E ⊗[k] (Fin n → R)) →ₗ[E ⊗[k] R] (E ⊗[k] N)) ≃ₗ[E]
      (Fin n → E ⊗[k] N) :=
  (LinearEquiv.congrLeft (E ⊗[k] N) E (scalarExtensionPi k E R n)).trans
    (LinearEquiv.piRing (E ⊗[k] R) (E ⊗[k] N) (Fin n) E)

theorem scalarExtensionHom_bijective_pi (n : ℕ) :
    Function.Bijective (scalarExtensionHom k E R (M := Fin n → R) (N := N)) := by
  let s : (E ⊗[k] ((Fin n → R) →ₗ[R] N)) ≃ₗ[E] (Fin n → E ⊗[k] N) :=
    ((LinearEquiv.piRing R N (Fin n) k).baseChange k E).trans
      (TensorProduct.piRight k E E (fun _ : Fin n => N))
  let t := scalarExtensionHomCoordinates k E R (N := N) n
  have heq : t.toLinearMap.comp (scalarExtensionHom k E R) = s.toLinearMap := by
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul e f =>
      funext i
      change (scalarExtensionHom k E R (e ⊗ₜ[k] f))
        ((scalarExtensionPi k E R n).symm (Pi.single i 1)) = e ⊗ₜ[k] f (Pi.single i 1)
      have hi : (scalarExtensionPi k E R n).symm (Pi.single i 1) =
          (1 : E) ⊗ₜ[k] (Pi.single i (1 : R)) := by
        change (TensorProduct.piRight k E E (fun _ : Fin n => R)).symm
          (Pi.single i ((1 : E) ⊗ₜ[k] (1 : R))) = _
        exact TensorProduct.piRight_symm_single k E E _ 1 i 1
      rw [hi, scalarExtensionHom_tmul]
      simp only [LinearMap.smul_apply, scalarExtensionMap_tmul,
        TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have heq_apply (x) : t (scalarExtensionHom k E R x) = s x :=
    LinearMap.congr_fun heq x
  constructor
  · intro x y h
    apply s.injective
    rw [← heq_apply, ← heq_apply, h]
  · intro f
    obtain ⟨x, hx⟩ := s.surjective (t f)
    exact ⟨x, t.injective ((heq_apply x).trans hx)⟩

theorem scalarExtensionHom_precomp (f : M →ₗ[R] N) (x : E ⊗[k] (N →ₗ[R] L)) :
    scalarExtensionHom k E R ((LinearMap.lcomp k L f).baseChange E x) =
      (scalarExtensionHom k E R x).comp (scalarExtensionMap k E R f) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy, LinearMap.add_comp]
  | tmul e g =>
    simp only [LinearMap.baseChange_tmul, LinearMap.lcomp_apply',
      scalarExtensionHom_tmul, scalarExtensionMap_comp, LinearMap.smul_comp]

theorem scalarExtensionHom_bijective [Module.Finite R M] [Module.Projective R M] :
    Function.Bijective (scalarExtensionHom k E R (M := M) (N := N)) := by
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' R M
  obtain ⟨s, hs⟩ := Module.projective_lifting_property p (LinearMap.id : M →ₗ[R] M) hp
  let a := (LinearMap.lcomp k N p).baseChange E
  let b := (LinearMap.lcomp k N s).baseChange E
  have hba (x : E ⊗[k] (M →ₗ[R] N)) : b (a x) = x := by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul e f =>
      change e ⊗ₜ[k] (f.comp p).comp s = e ⊗ₜ[k] f
      rw [LinearMap.comp_assoc, hs, LinearMap.comp_id]
  have hfree := scalarExtensionHom_bijective_pi k E R (N := N) n
  constructor
  · intro x y h
    have hxy : a x = a y := hfree.1 (by
      simp only [a, scalarExtensionHom_precomp, h])
    exact (hba x).symm.trans ((congrArg b hxy).trans (hba y))
  · intro f
    obtain ⟨x, hx⟩ := hfree.2 (f.comp (scalarExtensionMap k E R p))
    refine ⟨b x, ?_⟩
    rw [show b = (LinearMap.lcomp k N s).baseChange E from rfl,
      scalarExtensionHom_precomp, hx, LinearMap.comp_assoc,
      ← scalarExtensionMap_comp, hs, scalarExtensionMap_id, LinearMap.comp_id]

def scalarExtensionHomEquiv [Module.Finite R M] [Module.Projective R M] :
    E ⊗[k] (M →ₗ[R] N) ≃ₗ[E]
      ((E ⊗[k] M) →ₗ[E ⊗[k] R] (E ⊗[k] N)) :=
  LinearEquiv.ofBijective (scalarExtensionHom k E R)
    (scalarExtensionHom_bijective k E R)

end ArExplicit

end

end OAI
