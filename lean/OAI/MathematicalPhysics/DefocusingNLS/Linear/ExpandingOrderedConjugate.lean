import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingOrderedEnergy
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingNonlinearity

namespace OAI

/-! # Real differentiation commutes with physical complex conjugation -/

open scoped ComplexConjugate

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem homogeneousOrderedSymbol_conjugate (N : ℕ) (j : Fin N → Fin 12) (ξ : E) :
    conj (homogeneousOrderedSymbol N j (-ξ)) = homogeneousOrderedSymbol N j ξ := by
  simp only [homogeneousOrderedSymbol, map_prod]
  apply Finset.prod_congr rfl
  intro i _
  change conj ((-(ξ (j i)) : ℝ) * Complex.I) = (ξ (j i) : ℂ) * Complex.I
  simp only [map_mul, Complex.conj_ofReal, map_neg, Complex.conj_I, Complex.ofReal_neg]
  ring

theorem expandingOrderedMultiplier_conjugate (a L : ℝ) (N : ℕ)
    (j : Fin N → Fin 12) (n : frequencyLattice) :
    conj (expandingOrderedMultiplier a L N j (-n)) = expandingOrderedMultiplier a L N j n := by
  simp only [expandingOrderedMultiplier, map_mul, Complex.conj_ofReal,
    Submodule.coe_neg, homogeneousOrderedSymbol_conjugate]
  congr 2
  simp only [expandingSobolevWeight, expandingSobolevWeightSq, norm_neg]

theorem expandingOrderedFourierEnergy_conjugate (a L : ℝ) (N : ℕ) (hL : 1 ≤ L)
    (j : Fin N → Fin 12) (f : FourierL2) :
    expandingOrderedFourierEnergy a L N hL j (fourierConjugate f) =
      fourierConjugate (expandingOrderedFourierEnergy a L N hL j f) := by
  ext n
  simp only [expandingOrderedFourierEnergy_apply, fourierConjugate_apply, map_mul,
    expandingOrderedMultiplier_conjugate]

end DefocusingNLS

end OAI
