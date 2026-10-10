import OAI.NumberTheory.DirichletL.Detector.InitialSubseries
import OAI.NumberTheory.DirichletL.Detector.ContourShear

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeCompleted ProbeRow CompletedGauss CanonicalQuadraticSieve CubicEisenstein
open EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

def rawPhysicalMellinTerm (η : HeckeFamily.Character) (C : CalibrationData)
    (S : Finset (Ideal O)) (D I J K : Ideal O) (hK : Supported K)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (H : O) (t w z : ℂ) : ℂ :=
  physicalMellinCoefficientTerm η C S D I J (primaryGenerator K)
    ((supported_span_primaryGenerator_iff K).mpr hK) X H t z *fullIdealWeight w K*
    (Y:ℂ)^(w-1)*(Z:ℂ)^t*Complex.exp (t^2)*mellin (paperRadialFourier W0) z*mellin W1 w

theorem rawPhysicalMellinTerm_eq_source (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (D I J K : Ideal O) (hK : Supported K)
    (hKS : ∀P∈S,¬P∣K) (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z : ℝ) (hX : 0<X) (H : NonzeroFrequency) (t w z : ℂ) :
    rawPhysicalMellinTerm η (calibrationForSet S hS) S D I J K hK W0 W1 X Y Z H.val t w z=
      sourceMellinWeight W0 W1 X Y Z (t+1-z) w z *
        fullHighCoefficient S D η (fun h=>star ((calibrationForSet S hS).residueMonoid h.val))
          (t+1-z) w z (rawHighEmbedding (H,((I,J),K))) := by
  have hcs : IsCoprime (calibrationForSet S hS).generator (primaryGenerator K) := by
    apply calibrationForSet_coprime_of_excluded S hS
    rw [(primaryGenerator_spec K (supported_primaryGenerator_ne_zero K hK)).1]
    exact hKS
  unfold rawPhysicalMellinTerm
  rw [physicalMellinCoefficientTerm_eq_guarded η S hS hbad D I J (primaryGenerator K)
    ((supported_span_primaryGenerator_iff K).mpr hK) hcs X hX H.val H.property t z,
    guardedHighMellinCoefficient_eq_high η (calibrationForSet S hS) S hpS D I J K hK hKS X H.val
      (t+1-z) w z,sourceMellinWeight_shear]
  simp only [fullHighCoefficient,frequencyWeight,rawHighEmbedding]
  ring

end SevenEighths.ProbePhysical
end

end OAI
