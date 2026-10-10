import Mathlib

namespace OAI



open Filter Asymptotics
open scoped Topology

namespace QuarticPowerFree

def PowerFree (k : ℕ) (a : ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ¬ (p : ℤ) ^ k ∣ a

def rho (f : Polynomial ℤ) (q : ℕ) : ℕ :=
  ((Finset.range q).filter fun a : ℕ => (q : ℤ) ∣ f.eval (a : ℤ)).card

noncomputable def count (f : Polynomial ℤ) (k : ℕ) (X : ℝ) : ℕ := by
  classical
  exact ((Finset.Icc 1 ⌊X⌋₊).filter fun n : ℕ => PowerFree k (f.eval (n : ℤ))).card

def LocallyAdmissible (f : Polynomial ℤ) (k : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → rho f (p ^ k) < p ^ k

noncomputable def localFactor (f : Polynomial ℤ) (k : ℕ) (p : Nat.Primes) : ℝ :=
  1 - (rho f (p.val ^ k) : ℝ) / (p.val : ℝ) ^ k

noncomputable def densityConstant (f : Polynomial ℤ) (k : ℕ) : ℝ :=
  ∏' p : Nat.Primes, localFactor f k p

def DensityStatement (f : Polynomial ℤ) (k : ℕ) : Prop :=
  Multipliable (localFactor f k) ∧
  0 < densityConstant f k ∧
  (fun X : ℝ => (count f k X : ℝ) - densityConstant f k * X) =o[atTop]
    (fun X : ℝ => X)

theorem allDegrees (f : Polynomial ℤ)
    (hirr : Irreducible (f.map (Int.castRingHom ℚ)))
    (hdeglo : 4 ≤ f.natDegree)
    (hlocal : LocallyAdmissible f (f.natDegree - 2)) :
    DensityStatement f (f.natDegree - 2) := by
  sorry

end QuarticPowerFree

end OAI
