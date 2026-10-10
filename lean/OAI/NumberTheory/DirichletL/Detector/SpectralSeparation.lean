import OAI.NumberTheory.DirichletL.Detector.Row
import OAI.NumberTheory.DirichletL.Detector.PhysicalCoefficient

namespace OAI

noncomputable section
namespace SevenEighths.ProbeRow
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open ProbeCompleted
local notation "O" => ActualEisensteinCubic.O

def baseRowCoefficient (η : HeckeFamily.Character) (Xi : O →* ℂ)
    (s : O) (hs : Supported (Ideal.span {s})) : O →* ℂ :=
  targetMonoid η * InitialMeanSquare.conjugateMonoid Xi * reciprocityPhaseMonoid s hs

lemma spectralSummand_mul_fixed_twist (S : Finset (Ideal O)) (D I J : Ideal O)
    (φ Ψ : O →* ℂ) (t : ℂ) :
    spectralSummand S D (φ*Ψ) t I J =
      φ (completedIndex I J) * spectralSummand S D Ψ t I J := by
  have hc (η : O →* ℂ) : cubeWeight η J =
      star (FiniteGaussPhase.angularFactor (primaryGenerator J))^3 *
        η (primaryGenerator J)^3 / (Ideal.absNorm J:ℂ) := rfl
  unfold spectralSummand
  rw [hc, hc]
  simp only [columnWeight, MonoidHom.mul_apply, map_mul, map_pow, mul_pow, completedIndex]
  ring

theorem spectralSummand_row_separation (S : Finset (Ideal O)) (D I J : Ideal O)
    (η : HeckeFamily.Character) (Xi : O →* ℂ) (s : O)
    (hs : Supported (Ideal.span {s})) (m : O) (t : ℂ) :
    spectralSummand S D (rowCoefficient η Xi s hs m) t I J =
      idealRowHom m (Ideal.span {completedIndex I J}) *
        spectralSummand S D (baseRowCoefficient η Xi s hs) t I J := by
  have hr : rowCoefficient η Xi s hs m =
      ((idealRowHom m).toMonoidHom.comp principalIdealHom.toMonoidHom) *
        baseRowCoefficient η Xi s hs := by
    change _ * _ = _ * _
    exact mul_comm _ _
  rw [hr, spectralSummand_mul_fixed_twist]
  rfl

theorem calibrated_spectralSummand_separation (S : Finset (Ideal O)) (D I J : Ideal O)
    (η : HeckeFamily.Character) (C : ProbePhysical.CalibrationData) (s : O)
    (hs : Supported (Ideal.span {s})) (m : O) (t : ℂ) :
    C.residueMonoid m * spectralSummand S D (rowCoefficient η C.Xi s hs m) t I J =
      ProbePhysical.calibratedNumerator C (completedIndex I J) m *
        spectralSummand S D (baseRowCoefficient η C.Xi s hs) t I J := by
  rw [spectralSummand_row_separation]
  unfold ProbePhysical.calibratedNumerator
  ring

theorem spectralSummand_zero_completedIndex (S : Finset (Ideal O)) (D I J : Ideal O)
    (Ψ : O →* ℂ) (t : ℂ) (hz : completedIndex I J=0) :
    spectralSummand S D Ψ t I J=0 := by
  rcases mul_eq_zero.mp hz with hI | hJ
  · have hg : squarefreeGaussCoefficient I=0 := by
      unfold squarefreeGaussCoefficient
      rw [dite_eq_right (by simp [hI])]
    simp only [spectralSummand, columnWeight, hg, zero_mul, zero_div, mul_zero]
  · have hJ' : primaryGenerator J=0 := (pow_eq_zero_iff (by decide : 3≠0)).mp hJ
    have hc : cubeWeight Ψ J=0 := by
      change star (FiniteGaussPhase.angularFactor (primaryGenerator J))^3 *
        Ψ (primaryGenerator J)^3 / (Ideal.absNorm J:ℂ)=0
      simp [hJ', FiniteGaussPhase.angularFactor]
    simp only [spectralSummand, hc, mul_zero, zero_mul]

end SevenEighths.ProbeRow
end

end OAI
