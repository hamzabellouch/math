import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

universe u v

namespace Kadison

variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [CompleteSpace K]

def commutatorSeminorm (P : VonNeumannAlgebra K) (Y : K →L[ℂ] K) : ℝ :=
  sSup {r : ℝ | ∃ a : K →L[ℂ] K, a ∈ P ∧ ‖a‖ ≤ 1 ∧ r = ‖Y * a - a * Y‖}

def matrixOperator (h : ℕ) (X : Matrix (Fin h) (Fin h) (K →L[ℂ] K)) :
    (PiLp 2 fun _ : Fin h => K) →L[ℂ] (PiLp 2 fun _ : Fin h => K) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin h => K)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => ∑ j : Fin h,
      (X i j).comp (PiLp.proj 2 (fun _ : Fin h => K) j)))

def diagonalAmplification (h : ℕ) (Y : K →L[ℂ] K) :
    (PiLp 2 fun _ : Fin h => K) →L[ℂ] (PiLp 2 fun _ : Fin h => K) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin h => K)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => Y.comp (PiLp.proj 2 (fun _ : Fin h => K) i)))

end Kadison

end

end
end

end OAI
