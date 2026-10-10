import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorProjective
import Mathlib.LinearAlgebra.Pi

namespace OAI

noncomputable section
open scoped TensorProduct
namespace ArExplicit.ExternalTensor
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable {M N U V : Type u}
variable [AddCommGroup M] [AddCommGroup N] [AddCommGroup U] [AddCommGroup V]
variable [Module k M] [Module k N] [Module k U] [Module k V]
variable [Module A M] [Module B N] [Module A U] [Module B V]
variable [IsScalarTower k A M] [IsScalarTower k B N] [IsScalarTower k A U] [IsScalarTower k B V]

def homPair : (M →ₗ[A] U) →ₗ[k] (N →ₗ[B] V) →ₗ[k]
    (moduleObject k A B M N →ₗ[A ⊗[k] B] moduleObject k A B U V) :=
  LinearMap.mk₂ k (map k A B)
    (fun f f' g => by
      apply LinearMap.restrictScalars_injective k
      apply TensorProduct.ext
      apply LinearMap.ext
      intro x
      apply LinearMap.ext
      intro y
      exact TensorProduct.add_tmul _ _ _)
    (fun a f g => by
      apply LinearMap.restrictScalars_injective k
      apply TensorProduct.ext
      apply LinearMap.ext
      intro x
      apply LinearMap.ext
      intro y
      exact TensorProduct.smul_tmul' a (f x) (g y))
    (fun f g g' => by
      apply LinearMap.restrictScalars_injective k
      apply TensorProduct.ext
      apply LinearMap.ext
      intro x
      apply LinearMap.ext
      intro y
      exact TensorProduct.tmul_add _ _ _)
    (fun a f g => by
      apply LinearMap.restrictScalars_injective k
      apply TensorProduct.ext
      apply LinearMap.ext
      intro x
      apply LinearMap.ext
      intro y
      exact TensorProduct.tmul_smul a (f x) (g y))

def homMap : (M →ₗ[A] U) ⊗[k] (N →ₗ[B] V) →ₗ[k]
    (moduleObject k A B M N →ₗ[A ⊗[k] B] moduleObject k A B U V) :=
  TensorProduct.lift (homPair k A B)

@[simp] theorem homMap_tmul (f : M →ₗ[A] U) (g : N →ₗ[B] V) :
    homMap k A B (f ⊗ₜ[k] g) = map k A B f g := rfl

def freeFlatEquiv (n m : ℕ) :
    moduleObject k A B (Fin n → A) (Fin m → B) ≃ₗ[A ⊗[k] B]
      (Fin n × Fin m → A ⊗[k] B) :=
  (freeEquiv k A B n m).trans (LinearEquiv.curry _ _ (Fin n) (Fin m)).symm

@[simp] theorem freeFlatEquiv_tmul (n m : ℕ) (a : Fin n → A) (b : Fin m → B)
    (i : Fin n) (j : Fin m) :
    freeFlatEquiv k A B n m (a ⊗ₜ[k] b) (i,j) = a i ⊗ₜ[k] b j :=
  freeCoordinates_tmul k A B n m a b i j

theorem freeFlatEquiv_symm_single (n m : ℕ) (i : Fin n) (j : Fin m) :
    (freeFlatEquiv k A B n m).symm (Pi.single (i,j) 1) =
      (Pi.single i (1 : A)) ⊗ₜ[k] (Pi.single j (1 : B)) := by
  apply (freeFlatEquiv k A B n m).injective
  rw [LinearEquiv.apply_symm_apply]
  funext ⟨i',j'⟩
  rw [freeFlatEquiv_tmul]
  by_cases hi : i'=i <;> by_cases hj : j'=j <;>
    simp [hi, hj, Prod.mk.injEq, Algebra.TensorProduct.one_def]

def homFreeCoordinates (n m : ℕ) :
    (moduleObject k A B (Fin n → A) (Fin m → B) →ₗ[A ⊗[k] B] moduleObject k A B U V) ≃ₗ[k]
      (Fin n × Fin m → moduleObject k A B U V) :=
  (LinearEquiv.congrLeft (moduleObject k A B U V) k (freeFlatEquiv k A B n m)).trans
    (LinearEquiv.piRing (A ⊗[k] B) (moduleObject k A B U V) (Fin n × Fin m) k)

theorem homMap_bijective_free (n m : ℕ) :
    Function.Bijective (homMap k A B (M := Fin n → A) (N := Fin m → B) (U := U) (V := V)) := by
  let s : (((Fin n → A) →ₗ[A] U) ⊗[k] ((Fin m → B) →ₗ[B] V)) ≃ₗ[k]
      (Fin n × Fin m → U ⊗[k] V) :=
    (TensorProduct.congr (LinearEquiv.piRing A U (Fin n) k)
      (LinearEquiv.piRing B V (Fin m) k)).trans
      ((TensorProduct.piLeft k (Fin m → V) (fun _ : Fin n => U)).trans
        ((LinearEquiv.piCongrRight fun _ => TensorProduct.piRight k k U (fun _ : Fin m => V)).trans
          (LinearEquiv.curry k (U ⊗[k] V) (Fin n) (Fin m)).symm))
  let t := homFreeCoordinates k A B (U := U) (V := V) n m
  have heq (x) : t (homMap k A B x) = s x := by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]; rfl
    | tmul f g =>
      funext ⟨i,j⟩
      change homMap k A B (f ⊗ₜ[k] g)
        ((freeFlatEquiv k A B n m).symm (Pi.single (i,j) 1)) = _
      rw [freeFlatEquiv_symm_single, homMap_tmul, map_tmul]
      rfl
  constructor
  · intro x y hxy
    exact s.injective ((heq x).symm.trans ((congrArg t hxy).trans (heq y)))
  · intro f
    obtain ⟨x,hx⟩ := s.surjective (t f)
    exact ⟨x,t.injective ((heq x).trans hx)⟩

variable {M' N' : Type u} [AddCommGroup M'] [AddCommGroup N']
variable [Module k M'] [Module k N'] [Module A M'] [Module B N']
variable [IsScalarTower k A M'] [IsScalarTower k B N']

theorem homMap_precomp (f : M' →ₗ[A] M) (g : N' →ₗ[B] N)
    (x : (M →ₗ[A] U) ⊗[k] (N →ₗ[B] V)) :
    homMap k A B ((TensorProduct.map (LinearMap.lcomp k U f) (LinearMap.lcomp k V g)) x) =
      (homMap k A B x).comp (map k A B f g) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy, LinearMap.add_comp]
  | tmul u v =>
    apply LinearMap.restrictScalars_injective k
    apply TensorProduct.ext
    apply LinearMap.ext
    intro m
    apply LinearMap.ext
    intro n
    rfl

theorem homMap_bijective [Module.Finite A M] [Module.Projective A M]
    [Module.Finite B N] [Module.Projective B N] :
    Function.Bijective (homMap k A B (M := M) (N := N) (U := U) (V := V)) := by
  obtain ⟨n,p,hp⟩ := Module.Finite.exists_fin' A M
  obtain ⟨m,q,hq⟩ := Module.Finite.exists_fin' B N
  obtain ⟨s,hs⟩ := Module.projective_lifting_property p (LinearMap.id : M →ₗ[A] M) hp
  obtain ⟨t,ht⟩ := Module.projective_lifting_property q (LinearMap.id : N →ₗ[B] N) hq
  let a := TensorProduct.map (LinearMap.lcomp k U p) (LinearMap.lcomp k V q)
  let b := TensorProduct.map (LinearMap.lcomp k U s) (LinearMap.lcomp k V t)
  have hba (x : (M →ₗ[A] U) ⊗[k] (N →ₗ[B] V)) : b (a x) = x := by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul u v =>
      change ((u.comp p).comp s) ⊗ₜ[k] ((v.comp q).comp t) = u ⊗ₜ[k] v
      rw [LinearMap.comp_assoc, LinearMap.comp_assoc, hs, ht, LinearMap.comp_id, LinearMap.comp_id]
  have hsplit : (map k A B p q).comp (map k A B s t) = LinearMap.id := by
    apply LinearMap.restrictScalars_injective k
    apply TensorProduct.ext
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change p (s x) ⊗ₜ[k] q (t y) = x ⊗ₜ[k] y
    rw [show p (s x) = x from DFunLike.congr_fun hs x,
      show q (t y) = y from DFunLike.congr_fun ht y]
  have hfree := homMap_bijective_free k A B (U := U) (V := V) n m
  constructor
  · intro x y hxy
    have hab : a x = a y := hfree.1 (by simp only [a, homMap_precomp, hxy])
    exact (hba x).symm.trans ((congrArg b hab).trans (hba y))
  · intro f
    obtain ⟨x,hx⟩ := hfree.2 (f.comp (map k A B p q))
    refine ⟨b x, ?_⟩
    rw [show b = TensorProduct.map (LinearMap.lcomp k U s) (LinearMap.lcomp k V t) from rfl,
      homMap_precomp, hx, LinearMap.comp_assoc, hsplit, LinearMap.comp_id]

def homEquiv [Module.Finite A M] [Module.Projective A M]
    [Module.Finite B N] [Module.Projective B N] :
    (M →ₗ[A] U) ⊗[k] (N →ₗ[B] V) ≃ₗ[k]
      (moduleObject k A B M N →ₗ[A ⊗[k] B] moduleObject k A B U V) :=
  LinearEquiv.ofBijective (homMap k A B) (homMap_bijective k A B)

end ArExplicit.ExternalTensor

end

end OAI
