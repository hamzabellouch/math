import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootBruhatResidues
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFiniteFourierParseval

namespace OAI

/-! Actual finite Fourier projections for the fractional root action.
The character is the codifferent pairing already used by the arithmetic rows. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def cubicThetaPrimeRootFourierProjection {p : Eisenstein} (hp : primaryPrime p)
    (k : Residues p) : cubicThetaPrimeRootSections p →ₗ[ℂ] cubicThetaPrimeRootSections p := by
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Fintype (Residues p) := Fintype.ofFinite _
  exact (norm p:ℂ)⁻¹ • ∑ r : Residues p,
    star (residueFourierChar p hp.2.ne_zero (k*r)) • (cubicThetaPrimeRootResidueOperator hp r).toLinearMap

lemma cubicThetaPrimeRootFourierProjection_apply {p : Eisenstein} (hp : primaryPrime p)
    [Fintype (Residues p)] (k : Residues p) (F : cubicThetaPrimeRootSections p) :
    cubicThetaPrimeRootFourierProjection hp k F=
      (norm p:ℂ)⁻¹ • ∑ r : Residues p,
        star (residueFourierChar p hp.2.ne_zero (k*r)) • cubicThetaPrimeRootResidueOperator hp r F := by
  classical
  simp only [cubicThetaPrimeRootFourierProjection,LinearMap.smul_apply,LinearMap.sum_apply,
    LinearEquiv.coe_toLinearMap]
  congr 1
  apply Finset.sum_congr
  · ext r
    simp
  · intro r _
    rfl

lemma cubicThetaPrimeRootFourierProjection_translate {p : Eisenstein} (hp : primaryPrime p)
    (k s : Residues p) (F : cubicThetaPrimeRootSections p) :
    cubicThetaPrimeRootFourierProjection hp k (cubicThetaPrimeRootResidueOperator hp s F)=
      residueFourierChar p hp.2.ne_zero (k*s) • cubicThetaPrimeRootFourierProjection hp k F := by
  classical
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Fintype (Residues p) := Fintype.ofFinite _
  let ψ := residueFourierChar p hp.2.ne_zero
  have hc (r : Residues p) : star (ψ (k*r))=ψ (k*s)*star (ψ (k*(r+s))) := by
    simp only [ψ,cubicThetaResidueFourier_star]
    rw [←AddChar.map_add_eq_mul]
    congr 1
    ring
  rw [cubicThetaPrimeRootFourierProjection_apply]
  simp_rw [←cubicThetaPrimeRootResidueOperator_add]
  calc
    _ = (norm p:ℂ)⁻¹ • ∑ r : Residues p,ψ (k*s) •
        (star (ψ (k*(r+s))) • cubicThetaPrimeRootResidueOperator hp (r+s) F) := by
      congr 1
      apply Finset.sum_congr rfl
      intro r _
      rw [smul_smul,←hc r]
    _ = ψ (k*s) • ((norm p:ℂ)⁻¹ • ∑ r : Residues p,
        star (ψ (k*(r+s))) • cubicThetaPrimeRootResidueOperator hp (r+s) F) := by
      rw [←Finset.smul_sum,smul_comm]
    _ = _ := by
      have he := Equiv.sum_comp (Equiv.addRight s)
        (fun r => star (ψ (k*r)) • cubicThetaPrimeRootResidueOperator hp r F)
      change (∑ r : Residues p,star (ψ (k*(r+s))) • cubicThetaPrimeRootResidueOperator hp (r+s) F)=
        ∑ r : Residues p,star (ψ (k*r)) • cubicThetaPrimeRootResidueOperator hp r F at he
      rw [he,cubicThetaPrimeRootFourierProjection_apply]

lemma cubicThetaPrimeRootFourierProjection_zero {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeRootFourierProjection hp 0=cubicThetaPrimeRootAverage hp := by
  classical
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Fintype (Residues p) := Fintype.ofFinite _
  ext F
  simp [cubicThetaPrimeRootFourierProjection_apply,cubicThetaPrimeRootAverage_apply]

end CubicFirstMoment

end

end OAI
