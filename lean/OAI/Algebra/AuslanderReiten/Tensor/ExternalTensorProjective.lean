import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorModule
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.LinearAlgebra.StdBasis

namespace OAI

noncomputable section
open scoped TensorProduct

namespace ArExplicit.ExternalTensor

universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]

def freeCoordinates (n m : ℕ) :
    (Fin n → A) ⊗[k] (Fin m → B) ≃ₗ[k] (Fin n → Fin m → A ⊗[k] B) :=
  (TensorProduct.piLeft k (Fin m → B) (fun _ : Fin n => A)).trans
    (LinearEquiv.piCongrRight fun _ => TensorProduct.piRight k k A (fun _ : Fin m => B))

@[simp] theorem freeCoordinates_tmul (n m : ℕ) (a : Fin n → A) (b : Fin m → B)
    (i : Fin n) (j : Fin m) :
    freeCoordinates k A B n m (a ⊗ₜ[k] b) i j = (a i) ⊗ₜ[k] (b j) := by
  simp [freeCoordinates, TensorProduct.piLeft, TensorProduct.piRight_apply,
    TensorProduct.piRightHom_tmul]

def freeEquiv (n m : ℕ) :
    moduleObject k A B (Fin n → A) (Fin m → B) ≃ₗ[A ⊗[k] B]
      (Fin n → Fin m → A ⊗[k] B) where
  __ := (freeCoordinates k A B n m).toAddEquiv
  map_smul' a z := by
    let w : (Fin n → A) ⊗[k] (Fin m → B) := z
    change freeCoordinates k A B n m (representation k A B _ _ a w) =
      a • freeCoordinates k A B n m w
    induction a using TensorProduct.inductionOn with
    | add a b ha hb => simp only [map_add, LinearMap.add_apply, add_smul, ha, hb]
    | tmul a b =>
      induction w using TensorProduct.inductionOn with
      | add x y hx hy => simp only [map_add, smul_add, hx, hy]
      | tmul x y =>
        funext i j
        change freeCoordinates k A B n m ((a • x) ⊗ₜ[k] (b • y)) i j =
          (a ⊗ₜ[k] b) * freeCoordinates k A B n m (x ⊗ₜ[k] y) i j
        simp only [freeCoordinates_tmul, Pi.smul_apply, smul_eq_mul,
          Algebra.TensorProduct.tmul_mul_tmul]

instance freeFree (n m : ℕ) :
    Module.Free (A ⊗[k] B) (moduleObject k A B (Fin n → A) (Fin m → B)) :=
  Module.Free.of_equiv (freeEquiv k A B n m).symm

variable {M N : Type u} [AddCommGroup M] [AddCommGroup N]
variable [Module k M] [Module k N] [Module A M] [Module B N]
variable [IsScalarTower k A M] [IsScalarTower k B N]

theorem projective [Module.Finite A M] [Module.Projective A M]
    [Module.Finite B N] [Module.Projective B N] :
    Module.Projective (A ⊗[k] B) (moduleObject k A B M N) := by
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' A M
  obtain ⟨m, q, hq⟩ := Module.Finite.exists_fin' B N
  obtain ⟨s, hs⟩ := Module.projective_lifting_property p (LinearMap.id : M →ₗ[A] M) hp
  obtain ⟨t, ht⟩ := Module.projective_lifting_property q (LinearMap.id : N →ₗ[B] N) hq
  apply Module.Projective.of_split (map k A B s t) (map k A B p q)
  apply LinearMap.ext
  intro z
  let w : M ⊗[k] N := z
  change TensorProduct.map (p.restrictScalars k) (q.restrictScalars k)
    (TensorProduct.map (s.restrictScalars k) (t.restrictScalars k) w) = w
  induction w using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
    simp only [TensorProduct.map_tmul, LinearMap.restrictScalars_apply,
      show p (s x) = x from DFunLike.congr_fun hs x,
      show q (t y) = y from DFunLike.congr_fun ht y]

end ArExplicit.ExternalTensor

end

end OAI
