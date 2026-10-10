import Mathlib
import OAI.Geometry.HyperbolicGroups.BoundaryRotation

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.WordPictures
variable {A : Type*} {R : Set (Word A)}
namespace SymmetricRelator
lemma filling {w : Word A} (h : SymmetricRelator R w) : Homotopy R w [] 1 := by
  rcases h with h | h
  · simpa using Homotopy.move (Move.face [] [] w h)
  · simpa using Homotopy.move (Move.reverseFace [] [] (FreeGroup.invRev w) h)
end SymmetricRelator
namespace Homotopy
lemma rotate_filling {w : Word A} {n : ℕ} (h : Homotopy R w [] n)
    (i : ℕ) (hi : i ≤ w.length) : Homotopy R (w.rotate i) [] n := by
  rw [List.rotate_eq_drop_append_take hi]
  apply Homotopy.rotate_null
  simpa only [List.take_append_drop] using h

/-- The paid step for peeling an actual adjacent relator: its first side is
paired to the first outside side. All other new boundary letters stay literal. -/
lemma peel {a b : A × Bool} {l r : Word A} {n : ℕ}
    (hp : b = invLetter a) (hr : Homotopy R (b::r) [] 1)
    (h : Homotopy R (r++l) [] n) : Homotopy R (a::l) [] (1+n) := by
  have h₁ : Homotopy R (a::l) (a::b::(r++l)) 1 := by
    simpa only [List.singleton_append,List.cons_append,List.nil_append] using
      (hr.contextual [a] l).symm
  have hf : FreeGroup.mk [a,b] = 1 := by
    rw [hp]
    change FreeGroup.mk ([a] ++ FreeGroup.invRev [a]) = 1
    rw [← FreeGroup.mul_mk,← FreeGroup.inv_mk,mul_inv_cancel]
  have h₂ : Homotopy R (a::b::(r++l)) (r++l) 0 := Homotopy.free (by
    change FreeGroup.mk ([a,b]++(r++l)) = _
    rw [← FreeGroup.mul_mk,hf,one_mul])
  simpa only [Nat.add_zero] using (h₁.trans h₂).trans h
end Homotopy
end HyperbolicObstruction.WordPictures
end
end

section

end
end

end OAI
