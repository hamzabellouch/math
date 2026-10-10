import OAI.MathematicalPhysics.DefocusingNLS.Linear.TorusFourierProduct
import OAI.MathematicalPhysics.DefocusingNLS.Linear.TorusOrderedEnergy
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingOrderedSymbol
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingMultiplication

namespace OAI

/-! # The exact Fourier kernel of the physical product commutator -/

namespace DefocusingNLS

noncomputable def expandingProductCommutator (a L : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hN : 8 < (N : ℝ)) (hL : 1 ≤ L)
    (j : Fin N → Fin 12) (q f : FourierL2) : FourierL2 :=
  expandingOrderedFourierEnergy a L N hL j (expandingProduct a N L ha ha1 hN hL q f) -
    fourierConvolution (expandingFourierCoefficient a N L q)
      (expandingOrderedFourierEnergy a L N hL j f)

theorem expandingOrderedMultiplier_mul_weight (a L : ℝ) (N : ℕ) (hL : 1 ≤ L)
    (j : Fin N → Fin 12) (n : frequencyLattice) :
    expandingOrderedMultiplier a L N j n * (expandingSobolevWeight a N L n : ℂ) =
      (((2 * Real.pi) ^ 6 * L ^ (6 - (N : ℝ)) : ℝ) : ℂ) * homogeneousOrderedSymbol N j n := by
  unfold expandingOrderedMultiplier
  push_cast
  field_simp [(Complex.ofReal_ne_zero.mpr (expandingSobolevWeight_pos a N L hL n).ne')]

theorem expandingProductCommutator_kernel (a L : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hN : 8 < (N : ℝ)) (hL : 1 ≤ L)
    (j : Fin N → Fin 12) (q f : FourierL2) (n : frequencyLattice) :
    expandingProductCommutator a L N ha ha1 hN hL j q f n =
      ∑' m, expandingFourierCoefficient a N L q m *
        expandingOrderedDifference a L N j m (n - m) * f (n - m) := by
  let C : ℂ := (((2 * Real.pi) ^ 6 * L ^ (6 - (N : ℝ)) : ℝ) : ℂ)
  let A : frequencyLattice → ℂ := fun m => C * homogeneousOrderedSymbol N j n *
    (expandingFourierCoefficient a N L q m * expandingFourierCoefficient a N L f (n - m))
  let B : frequencyLattice → ℂ := fun m => expandingFourierCoefficient a N L q m *
    (expandingOrderedMultiplier a L N j (n - m) * f (n - m))
  have hA : Summable A :=
    (summable_expandingProductTerms a N L ha ha1 hN hL q f n).mul_left _
  have hB : Summable B := by
    have h := (summable_fourierConvolution_terms (expandingFourierCoefficient a N L q)
      (summable_norm_expandingFourierCoefficient a N L ha ha1 hN hL q)
      (expandingOrderedFourierEnergy a L N hL j f)).hasSum.mapL
        (lp.evalCLM ℂ (fun _ : frequencyLattice => ℂ) 2 n)
    have hs := h.summable
    change Summable (fun m => expandingFourierCoefficient a N L q m *
      expandingOrderedFourierEnergy a L N hL j f (n - m)) at hs
    simpa only [expandingOrderedFourierEnergy_apply, B] using hs
  have hterm (m : frequencyLattice) : A m - B m =
      expandingFourierCoefficient a N L q m *
        expandingOrderedDifference a L N j m (n - m) * f (n - m) := by
    have hm : ((n - m : frequencyLattice) : EuclideanSpace ℝ (Fin 12)) + m = n := by
      change (n : EuclideanSpace ℝ (Fin 12)) - m + m = n
      exact sub_add_cancel _ _
    dsimp only [A, B, C, expandingOrderedDifference, expandingOrderedFactor,
      expandingOrderedMultiplier, expandingFourierCoefficient]
    rw [hm]
    push_cast
    ring
  rw [show (fun m => expandingFourierCoefficient a N L q m *
      expandingOrderedDifference a L N j m (n - m) * f (n - m)) =
        (fun m => A m - B m) from funext (fun m => (hterm m).symm), hA.tsum_sub hB]
  change expandingOrderedFourierEnergy a L N hL j
      (expandingProduct a N L ha ha1 hN hL q f) n -
    fourierConvolution (expandingFourierCoefficient a N L q)
      (expandingOrderedFourierEnergy a L N hL j f) n = _
  rw [fourierConvolution_apply _ (summable_norm_expandingFourierCoefficient a N L ha ha1 hN hL q)]
  congr 1
  · change expandingOrderedMultiplier a L N j n *
      ((expandingSobolevWeight a N L n : ℂ) * expandingProductCoefficient a N L q f n) = _
    rw [← mul_assoc, expandingOrderedMultiplier_mul_weight a L N hL]
    exact (tsum_mul_left).symm

end DefocusingNLS

end OAI
