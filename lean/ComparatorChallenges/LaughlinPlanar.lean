import Mathlib

namespace OAI

namespace Laughlin
open scoped BigOperators Matrix ENNReal

noncomputable def gammaStar : ℝ := 4616733319001 / 10^14

noncomputable def pairLimitCoefficient (p x y : ℕ) : ℝ :=
  if x+y = p+1 then
    ((x : ℝ)-(y : ℝ)) * Real.sqrt ((p.factorial : ℝ) /
      (((2 : ℕ) : ℝ)^p * (x.factorial : ℝ) * (y.factorial : ℝ))) / Real.sqrt (2 : ℕ)
  else 0

namespace Fock

abbrev Orbital (Q : ℕ) := Fin (Q+1) → ℂ
abbrev Space (Q : ℕ) := ExteriorAlgebra ℂ (Orbital Q)

noncomputable def annihilate {Q : ℕ} (i : Fin (Q+1)) : Module.End ℂ (Space Q) :=
  CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ (Orbital Q))) (LinearMap.proj i)

noncomputable def occupationBasis (Q : ℕ) :
    Module.Basis (Finset (Fin (Q+1))) ℂ (Space Q) :=
  (Pi.basisFun ℂ (Fin (Q+1))).ExteriorAlgebra

def OccupationBidegree (Q n w : ℕ) (x : Space Q) : Prop :=
  ∀ A : Finset (Fin (Q+1)), (A.card ≠ n ∨ (∑ i ∈ A, i.val) ≠ w) →
    (occupationBasis Q).repr x A = 0

end Fock

namespace Planar
open Fock

abbrev Occupations (L : ℕ) := Finset (Fin (L+1))

noncomputable def pairMatrix (L : ℕ) (c : Fin (L+1) → Fin (L+1) → ℂ) :
    Matrix (Occupations L) (Occupations L) ℂ := fun A B =>
  ∑ i, ∑ j, c i j * (occupationBasis L).repr
    (annihilate j (annihilate i (occupationBasis L B))) A

noncomputable def planarCoefficient (p i j : ℕ) : ℂ :=
  ((pairLimitCoefficient p i j / Real.sqrt (2 : ℕ) : ℝ) : ℂ)

noncomputable def planarPairMatrix (L p : ℕ) : Matrix (Occupations L) (Occupations L) ℂ :=
  pairMatrix L (fun i j => planarCoefficient p i.val j.val)

noncomputable def planarHamiltonian (L : ℕ) : Matrix (Occupations L) (Occupations L) ℂ :=
  ∑ p ∈ Finset.range (2*L+1), (planarPairMatrix L p)ᴴ * planarPairMatrix L p

noncomputable def pairEnergy (L : ℕ)
    (P : ℕ → Matrix (Occupations L) (Occupations L) ℂ) (x : Occupations L → ℂ) : ℝ :=
  ∑ p ∈ Finset.range (2*L+1), ∑ A, ‖(P p *ᵥ x) A‖^2

noncomputable def squareNorm (L : ℕ) (H : Matrix (Occupations L) (Occupations L) ℂ)
    (x : Occupations L → ℂ) : ℝ := ∑ A, ‖(H *ᵥ x) A‖^2

/-- Occupation coefficients with fixed particle number in every homogeneous degree. -/
structure HomogeneousState (N : ℕ) where
  block : (L : ℕ) → Space L
  homogeneous : ∀ L, OccupationBidegree L N L (block L)

noncomputable def fullEnergy {N : ℕ} (ψ : HomogeneousState N) : ℝ≥0∞ :=
  ∑' L, ENNReal.ofReal (pairEnergy L (planarPairMatrix L)
    (fun A => (occupationBasis L).repr (ψ.block L) A))

noncomputable def fullSquareNorm {N : ℕ} (ψ : HomogeneousState N) : ℝ≥0∞ :=
  ∑' L, ENNReal.ofReal (squareNorm L (planarHamiltonian L)
    (fun A => (occupationBasis L).repr (ψ.block L) A))

end Planar

/-- The planar endpoint inequality in the homogeneous occupation representation. -/
theorem planar_gap {N : ℕ} (ψ : Planar.HomogeneousState N) :
    ENNReal.ofReal gammaStar * Planar.fullEnergy ψ ≤ Planar.fullSquareNorm ψ := by
  sorry

end Laughlin

end OAI
