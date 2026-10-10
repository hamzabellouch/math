import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Intersection.QuadraticSequence

namespace OAI


                                       
section

namespace MaximalSeshadri.EulerNumerics

theorem affine_of_coprime_differences (f : ℕ → ℤ) (a b : ℕ)
    (hab : Nat.Coprime a b) (c d : ℤ)
    (ha : ∀ n, f (n+a)-f n=c) (hb : ∀ n, f (n+b)-f n=d) (n : ℕ) :
    f n = (n : ℤ)*(f 1-f 0)+f 0 := by
  let g (n : ℕ) := f (n+1)-f n
  have per (a : ℕ) (c : ℤ) (hh : ∀ n, f (n+a)-f n=c) : Function.Periodic g a := by
    intro n
    dsimp [g]
    have h1 := hh (n+1)
    have h0 := hh n
    rw [show n+1+a = n+a+1 by omega] at h1
    omega
  have hg (n : ℕ) : g n = g 0 := periodic_nat_coprime_constant g a b hab (per a c ha) (per b d hb) n
  induction n with
  | zero => simp
  | succ n ih =>
    have h := hg n
    dsimp [g] at h
    rw [ih] at h
    push_cast
    nlinarith
end MaximalSeshadri.EulerNumerics

end



end OAI
