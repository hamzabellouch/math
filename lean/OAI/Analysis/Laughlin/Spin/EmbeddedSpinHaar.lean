import OAI.Analysis.Laughlin.Spin.Disjoint
import OAI.Analysis.Laughlin.Spin.Sandwich

namespace OAI

namespace Laughlin.Rotation
open MeasureTheory
open scoped BigOperators Matrix

theorem embedded_spin_haar {I : Type*} [Fintype I] [DecidableEq I]
    (ρ : SourceSU2 →* Matrix I I ℂ) (hρ : ∀ g, ρ g⁻¹=(ρ g)ᴴ)
    (m : ℕ) (W : Matrix I (Fin (m+1)) ℂ)
    (hW : ∀ g, ρ g*W=W*sourceSpinRepresentation m g)
    (M : Matrix (Fin (m+1)) (Fin (m+1)) ℂ) :
    matrixIntegral sourceHaar (conjugateOrbit ρ (W*M*Wᴴ)) =
      (Matrix.trace M/(m+1 : ℕ)) • (W*Wᴴ) := by
  have ha (g : SourceSU2) : Wᴴ*ρ g⁻¹=sourceSpinRepresentation m g⁻¹*Wᴴ := by
    have h := congrArg Matrix.conjTranspose (hW g)
    simpa only [Matrix.conjTranspose_mul,← hρ,← sourceSpinRepresentation_inv] using h
  have he (g : SourceSU2) : conjugateOrbit ρ (W*M*Wᴴ) g =
      W*conjugateOrbit (sourceSpinRepresentation m) M g*Wᴴ := by
    unfold conjugateOrbit
    calc
      _ = (ρ g*W)*M*(Wᴴ*ρ g⁻¹) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hW,ha]; simp only [Matrix.mul_assoc]
  unfold matrixIntegral
  simp_rw [he]
  rw [integral_matrix_sandwich sourceHaar _
    (compact_conjugateOrbit_integrable sourceHaar _ (sourceSpinRepresentation_continuous m) M)]
  change W*matrixIntegral sourceHaar (conjugateOrbit (sourceSpinRepresentation m) M)*Wᴴ = _
  rw [source_spin_haar_schur,Matrix.mul_smul,Matrix.mul_one,Matrix.smul_mul]

end Laughlin.Rotation

end OAI
