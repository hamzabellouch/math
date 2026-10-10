import Mathlib

namespace OAI

section
section
section
noncomputable section
namespace CannonTriangleBoundary
open Finset

def cycle {V R : Type*} [Add R] (f : V → V → R) (a b c : V) := f a b+f b c+f c a

def signed {R : Type*} [Neg R] (b : Bool) (x : R) := if b then x else -x

lemma triangle_boundary_signs {D V : Type*} [Fintype D]
    (a b c : D → V) {u v w : V} (huv : u≠v) (huw : u≠w) (hvw : v≠w)
    (s t r : Bool)
    (h : ∀ f : V → V → ℤ,(∀ x y,f y x= -f x y) →
      (∑ d,cycle f (a d) (b d) (c d))=signed s (f u v)+signed t (f v w)+signed r (f w u)) :
    s=t ∧ s=r := by
  classical
  let fu : V → V → ℤ := fun x y=>(if x=u then 1 else 0)-(if y=u then 1 else 0)
  let fv : V → V → ℤ := fun x y=>(if x=v then 1 else 0)-(if y=v then 1 else 0)
  have H1 := h fu (by intro x y; dsimp [fu]; ring)
  have H2 := h fv (by intro x y; dsimp [fv]; ring)
  have hzero (g : V → ℤ) (x y z : V) : cycle (fun p q=>g p-g q) x y z=0 := by unfold cycle; ring
  simp only [fu,hzero,Finset.sum_const_zero] at H1
  simp only [fv,hzero,Finset.sum_const_zero] at H2
  cases s <;> cases t <;> cases r <;>
    simp [signed,huv,Ne.symm huv,Ne.symm huw,Ne.symm hvw] at H1 H2
  all_goals exact ⟨rfl,rfl⟩

end CannonTriangleBoundary

end
end
end
end

end OAI
