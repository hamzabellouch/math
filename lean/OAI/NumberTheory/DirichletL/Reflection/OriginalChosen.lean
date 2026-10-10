import OAI.NumberTheory.DirichletL.Reflection.Pullback

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ : Type*} [Fintype σ] {m f z : Eis} (D : GoodMaskRowData m f z)
variable (R I F Q₀ : Ideal Eis) (hR : R≠0) (hI : I≠0) (hF : Squarefree F)
    (hm : m≠0) (hf : Ideal.span {f}=F) (hz : Ideal.span {z}=I)
    (hbad : ∀ P∈fixedBadPrimes, P∣Ideal.span {m}*F)
    (hcop : IsCoprime Q₀ (rowResidualPart I (Ideal.span {m}*F)))
    (hpow : rowPowerfulPart R=rowPowerfulPart I)
    (hmask : rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))
variable (S : PrimeFamily σ) (B : Finset (FreeReflection.pool R (Ideal.span {m}*F) Q₀)) (T : Finset σ)
local notation "E" => D.primeFiberEquiv R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask
local notation "K" => rowResidualPart I (Ideal.span (Set.singleton m)*F)
local notation "hK" => rowResidualPart_admissible I (Ideal.span (Set.singleton m)*F) hbad
local notation "PS" => PrimeFamily.restrict (PrimeFamily.sum (freePrimeFamily D.movingIdeal Q₀ D.movingSupported) S) (markedActiveSet E B T)
local notation "PF" => PrimeFamily.reflected (PrimeFamily.restrict (poolPrimeFamily R (Ideal.span (Set.singleton m)*F) Q₀) B) K hK (S.restrict T)
local notation "EA" => markedActiveEquiv E B T

def originalChosenControlled {N a c : Eis} {mode : Bool}
    (C : ControlledStratumArithmetic (PF).generator N a c mode) :
    ControlledStratumArithmetic (PS).generator N a c mode :=
  pullbackControlled EA
    (funext (original_active_family_generator D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask S B T)) C

theorem original_chosen_reflected_source_eq {N a c : Eis} {mode : Bool}
    (C : ControlledStratumArithmetic (PF).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (W : ℝ→ℂ) (X : ℝ) :
    mixedReflectedValue (originalChosenControlled D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask S B T C)
      s (PS).generator_ne_zero hc (PS).generator_good
      (fun i => Sum.elim (fun P : FreePrimeIndex D.movingIdeal Q₀ =>
        (UniqueFactorizationMonoid.normalizedFactors D.movingIdeal).count P.val.val%6)
        (fun _ : σ => 0) i.val) (activeMarks (markedActiveSet E B T) markedSumSlots) W X =
    mixedReflectedValue C s (PF).generator_ne_zero hc (PF).generator_good
      (reflectedExponent (fun b : B => completedLocalExponent R F b.val.val)) (slotIndices B (PrimeIndex K) T) W X := by
  unfold originalChosenControlled
  rw [mixedReflectedValue_pullback]
  have hj : (fun x => Sum.elim (fun P : FreePrimeIndex D.movingIdeal Q₀ =>
        (UniqueFactorizationMonoid.normalizedFactors D.movingIdeal).count P.val.val%6)
        (fun _ : σ => 0) (EA x).val)=
      reflectedExponent (fun b : B => completedLocalExponent R F b.val.val) := by
    funext x
    exact original_active_exponent D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask B T x
  rw [hj,original_active_marks_eq_slots D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask B T]
end
end SevenEighths.InverseReflectedPhase

end OAI
