import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingMomentCommutator
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingCircularMoment
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingOrderedConjugate
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingOrderedCommutator

namespace OAI

/-! # The full scalar odd-power commutator in Fourier coordinates -/

namespace DefocusingNLS

attribute [local irreducible] expandingCircularCoefficient expandingAnticircularCoefficient
  expandingProduct expandingFourierCoefficient expandingOrderedFourierEnergy

noncomputable def expandingOddFourierCommutator (a L : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hN : 8 < (N : ℝ)) (hL : 1 ≤ L)
    (m : ℕ) (q f : FourierL2) (j : Fin N → Fin 12) : FourierL2 :=
  expandingOrderedFourierEnergy a L N hL j (expandingLinearizedPotential a N L ha ha1 hN hL m q f) -
    (-Complex.I) •
      (fourierConvolution (expandingFourierCoefficient a N L
        (expandingCircularCoefficient a N L ha ha1 hN hL m q))
          (expandingOrderedFourierEnergy a L N hL j f) +
       fourierConvolution (expandingFourierCoefficient a N L
        (expandingAnticircularCoefficient a N L ha ha1 hN hL m q))
          (fourierConjugate (expandingOrderedFourierEnergy a L N hL j f)))

theorem expandingOddFourierCommutator_eq (a L : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hN : 8 < (N : ℝ)) (hL : 1 ≤ L)
    (m : ℕ) (q f : FourierL2) (j : Fin N → Fin 12) :
    expandingOddFourierCommutator a L N ha ha1 hN hL m q f j =
      (-Complex.I) •
        (expandingProductCommutator a L N ha ha1 hN hL j
          (expandingCircularCoefficient a N L ha ha1 hN hL m q) f +
        expandingProductCommutator a L N ha ha1 hN hL j
          (expandingAnticircularCoefficient a N L ha ha1 hN hL m q) (fourierConjugate f)) := by
  unfold expandingOddFourierCommutator
  change expandingOrderedFourierEnergy a L N hL j
    ((-Complex.I) • fderiv ℝ (expandingOddPower a N L ha ha1 hN hL m) q f) - _ = _
  rw [map_smul, expandingOddPower_derivative_algebra a N L ha ha1 hN hL, map_add]
  simp only [expandingProductCommutator, expandingOrderedFourierEnergy_conjugate,
    smul_sub, smul_add]
  abel

end DefocusingNLS

end OAI
