import OAI.Algebra.OddKaplansky.MatrixUnits

namespace OAI

universe contextUniverse1 contextUniverse2

universe portUniverse1 portUniverse2 portUniverse3 portUniverse4 portUniverse5 portUniverse6 portUniverse7

section
namespace OddKaplansky.MatrixActions
noncomputable section
open scoped Classical BigOperators Matrix
variable {K : Type portUniverse1} {A : Type portUniverse2} {S : Type portUniverse3} [CommRing K] [Ring A] [Ring S] [Algebra K A] [Algebra K S]
variable (φ : S →ₗ[K] A)
def Represents (a : A) (s : S) : Prop := ∀ F : S, a * φ F = φ (s*F) ∧ φ F * a = φ (F*s)
lemma represents_one : Represents φ 1 1 := by intro F; simp
lemma represents_sub {a b : A} {s t : S} (ha : Represents φ a s) (hb : Represents φ b t) :
    Represents φ (a-b) (s-t) := by
  intro F
  constructor
  · rw [sub_mul,(ha F).1,(hb F).1,sub_mul,map_sub]
  · rw [mul_sub,(ha F).2,(hb F).2,mul_sub,map_sub]
lemma represents_mul {a b : A} {s t : S} (ha : Represents φ a s) (hb : Represents φ b t) :
    Represents φ (a*b) (s*t) := by
  intro F
  constructor
  · rw [mul_assoc,(hb F).1,(ha (t*F)).1,mul_assoc]
  · rw [← mul_assoc,(ha F).2,(hb (F*s)).2,mul_assoc]
lemma represents_pow {a : A} {s : S} (ha : Represents φ a s) (n : ℕ) : Represents φ (a^n) (s^n) := by
  induction n with
  | zero => simpa only [pow_zero] using represents_one φ
  | succ n ih => simpa only [pow_succ] using represents_mul φ ih ha
lemma annihilates_left {a : A} {s F : S} (ha : Represents φ a s) (hs : s*F=0) : a*φ F=0 := by rw [(ha F).1,hs,map_zero]
lemma annihilates_right {a : A} {s F : S} (ha : Represents φ a s) (hs : F*s=0) : φ F*a=0 := by rw [(ha F).2,hs,map_zero]
end
end OddKaplansky.MatrixActions

namespace OddKaplansky.TranslationMatrix
noncomputable section
open scoped Classical BigOperators Matrix
variable {K : Type portUniverse4} {H : Type portUniverse5} [CommRing K] [Group H] [sectionInstance17 : Fintype H]
def matrix (h : H) : Matrix H H K := fun x y => if x=h*y then 1 else 0
lemma mul_apply (h : H) {J : Type portUniverse6} (A : Matrix H J K) (x : H) (y : J) : (matrix (K := K) h * A) x y = A (h⁻¹*x) y := by
  rw [Matrix.mul_apply,Finset.sum_eq_single (h⁻¹*x)]
  · simp [matrix]
  · intro b _ hb
    have he : x ≠ h*b := by intro he; apply hb; rw [he,inv_mul_cancel_left]
    simp [matrix,he]
  · simp
lemma right_mul_apply (h : H) {J : Type portUniverse7} [Fintype J] (A : Matrix J H K) (x : J) (y : H) :
    (A * matrix (K := K) h) x y = A x (h*y) := by simp [Matrix.mul_apply,matrix]
lemma one
    {K : Type contextUniverse1}
    {H : Type contextUniverse2}
    [CommRing.{contextUniverse1} K]
    [Group.{contextUniverse2} H]
    [Fintype.{contextUniverse2} H] : matrix (K := K) (H := H) 1 = 1 := by ext x y; simp [matrix,Matrix.one_apply]
lemma mul (h g : H) : matrix (K := K) (h*g) = matrix (K := K) h * matrix (K := K) g := by
  ext x y
  rw [mul_apply]
  have he : x = (h*g)*y ↔ h⁻¹*x = g*y := by
    constructor
    · intro hh; rw [hh]; simp only [mul_assoc,inv_mul_cancel_left]
    · intro hh
      calc
        x = h*(h⁻¹*x) := (mul_inv_cancel_left h x).symm
        _ = (h*g)*y := by rw [hh,mul_assoc]
  simp only [matrix,he]
end
end OddKaplansky.TranslationMatrix

end

end OAI
