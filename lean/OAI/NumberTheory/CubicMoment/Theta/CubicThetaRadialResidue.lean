import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialDirichlet
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaProjectedConstant

namespace OAI

/-! The radial residue after the actual finite cubic-character average.
The remaining arithmetic normalization is explicit. -/
noncomputable section
open scoped BigOperators MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaResidueConstant_squarefree {r : Eisenstein} (hr : primary r)
    (hs : Squarefree r) [Fintype (Residues r)] :
    cubicThetaResidueConstant r hr=
      (∏ p∈primaryPrimeFactors r,((norm p:ℂ)-1))*(star cubicThetaSeriesConstant/3) := by
  have hcard := cubicThetaRamanujan_units hr 0
  simp only [zero_mul,additivePhase_zero,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    mul_one,←Nat.card_eq_fintype_card] at hcard
  rw [cubicThetaResidueConstant_units,←hcard]
  have hp := cubicThetaRamanujan_prod (primaryPrimeFactors r)
    (fun p hp => (primaryPrimeFactor_spec hr hp).1) 0
  rw [primaryPrimeFactors_prod hr hs] at hp
  simpa only [dvd_zero,ite_true] using congrArg
    (fun z : ℂ => z*(star cubicThetaSeriesConstant/3)) hp

lemma cubicThetaResidueRadialConstant (r : Eisenstein) (hr : primary r)
    [Fintype (Residues r)] :
    (∑ u : Residues r,cubicSymbol r (residueRepresentative r u)*
      cubicThetaProjectedRadialConstant (cubicThetaResidueCuspMatrix r hr (residueRepresentative r u))
        (cubicThetaResidueCuspPrimary r hr (residueRepresentative r u)))=
      cubicThetaResidueConstant r hr*((cubicThetaLevelScale r^(2/3:ℝ):ℝ):ℂ) := by
  unfold cubicThetaProjectedRadialConstant
  simp_rw [cubicThetaResidueCuspMatrix_bottom]
  unfold cubicThetaResidueConstant
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro u _
  ring

end CubicFirstMoment

end

end OAI
