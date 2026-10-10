import OAI.Combinatorics.PolynomialVacuum.Algebra.CupScalarCompatibility
import OAI.Combinatorics.PolynomialVacuum.Algebra.NaturalUnitary

namespace OAI

namespace PolynomialVacuumAlgebra
open Classical

 

def FirstCupReduction (Ψ ψ : NatSpectralTensor) (n : ℕ) : Prop :=
  ∀ X, X 1=T*X 0 → Ψ X=naturalFusion n 0 X • cupLinear 0 (ψ (skipTwo 0 X))

theorem naturalPrescription_firstCup_after {ψ φ : NatSpectralTensor} {m : ℕ}
    (hψ : FirstCupReduction ψ φ m) (j : ℕ) (hj : j ≤ m) (X : ℕ → ℂ)
    (hX : X 1=T*X 0) :
    naturalPrescription ψ (m+2) (j+2) X =
      naturalFusion (m+2) 0 (insertOne (m+3) (T*X (j+2)) X) •
        cupLinear 0 (naturalPrescription φ m j (skipTwo 0 X)) := by
  have he := hψ (skipOne (j+2) X) (by simpa [skipOne] using hX)
  have ho : braidTrain (T*X (j+2)) X (j+2+1) (m+2-(j+2))*cupLinear (j+2)*cupLinear 0=
      cupLinear 0*(braidTrain (T*X (j+2)) (skipTwo 0 X) (j+1) (m-j)*cupLinear j) := by
    rw [mul_assoc,cupLinear_cup_after (by omega : 0+2 ≤ j+2),← mul_assoc,
      braidTrain_cup_after 0 (j+2+1) _ (by omega)]
    simp only [show j+2-2=j by omega,show j+2+1-2=j+1 by omega,
      show m+2-(j+2)=m-j by omega,mul_assoc]
  unfold naturalPrescription
  rw [he,map_smul,smul_smul,← Module.End.mul_apply,ho,Module.End.mul_apply,
    skipTwo_skipOne_after,firstCup_scalar_compatibility m j hj X hX]
  simp only [skipTwo_zero_apply,map_smul,smul_smul]

theorem naturalPrescription_firstCup_middle (ψ : NatSpectralTensor) (n : ℕ)
    (X : ℕ → ℂ) (hX : X 1=T*X 0) : naturalPrescription ψ n 1 X=0 := by
  have hl : leftFusion 1 X=0 := by
    simp [leftFusion,hX,fusionPair_successor_zero]
  simp [naturalPrescription,hl]

end PolynomialVacuumAlgebra

end OAI
