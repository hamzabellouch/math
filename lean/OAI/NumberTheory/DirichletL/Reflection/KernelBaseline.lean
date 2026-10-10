import OAI.NumberTheory.DirichletL.Reflection.KernelActual

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open CompletedDyadic ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

theorem mixedReflectedValue_eq_actualKernelSource (F : PrimeFamily φ)
    (K : Ideal Eis) (hK : Admissible K) (S : PrimeFamily σ) (jF : φ→ℕ)
    (D : ControlledStratumArithmetic (F.reflected K hK S).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (W : ℝ→ℂ) (X : ℝ) :
    mixedReflectedValue D s (F.reflected K hK S).generator_ne_zero hc
      (F.reflected K hK S).generator_good (reflectedExponent jF) (slotIndices φ (PrimeIndex K) σ) W X =
    fixedRadialCoefficientScalar*s.stratumShapeFactor (c*∏ i, (F.reflected K hK S).generator i)*
      ∑' t : ThetaFullIndex,
        actualKernelSourceTerm F K hK S jF D s hc t.1 t.2.1 t.2.2.1.val t.2.2.2.val
          (fun _ _ => 1) 1 1 1 1 W 0 X := by
  unfold mixedReflectedValue
  congr 1
  apply tsum_congr
  intro t
  have hx : sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency t) =
      s.modelDualNumerator t.1 t.2.1 t.2.2.1.val t.2.2.2.val := by
    rw [thetaFullFrequency_eq_fixedCuspArrayIndex]
    rfl
  have hW : CompletedHeight.normTwistedSource W 0 = W := by
    funext x
    simp [CompletedHeight.normTwistedSource,FourierBridge.logPhase]
  unfold actualKernelSourceTerm actualMixedCoefficient
  rw [hx,hW]
  simp only [Finset.prod_const_one,one_div]
  ring

end
end SevenEighths.InverseReflectedPhase

end OAI
