import Mathlib

namespace OAI


                                                  
section
namespace MaximalSeshadri.EulerNumerics

def Quadratic (f : ℕ → ℤ) : Prop := ∀ n : ℕ,
  2*f n = (n : ℤ)*((n : ℤ)-1)*(f 2-2*f 1+f 0) +
    2*(n : ℤ)*(f 1-f 0)+2*f 0

lemma Quadratic.reindex (f : ℕ → ℤ) (hf : Quadratic f) (d : ℕ) :
    Quadratic (fun n => f (d*n)) := by
  intro n
  dsimp only
  have h := hf (d*n)
  have h2 := hf (d*2)
  have h1 := hf (d*1)
  simp only [Nat.mul_zero,Nat.mul_one] at h1 ⊢
  push_cast at h h2 h1
  have H : 2*(2*f (d*n) - ((n : ℤ)*((n : ℤ)-1)*(f (d*2)-2*f d+f 0) +
      2*(n : ℤ)*(f d-f 0)+2*f 0)) = 0 := by
    linear_combination 2*h - ((n : ℤ)*((n : ℤ)-1))*h2 +
      (2*(n : ℤ)*((n : ℤ)-2))*h1
  omega

theorem quadratic_of_twisted (f g h : ℕ → ℤ) (d : ℕ) (c j : ℤ)
    (hg : Quadratic g) (hh : Quadratic h)
    (he : ∀ n : ℕ, f n = g n - h (d*n) + c - (d : ℤ)*(n : ℤ)^2*j) :
    Quadratic f := by
  intro n
  have H := hg n
  have H' := Quadratic.reindex h hh d n
  simp only [Nat.mul_zero,Nat.mul_one] at H'
  rw [he n,he 2,he 1,he 0]
  norm_num only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,zero_pow,one_pow,
    Nat.mul_zero,Nat.mul_one]
  linear_combination H-H'
end MaximalSeshadri.EulerNumerics

end



end OAI
