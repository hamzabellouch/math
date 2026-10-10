import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootNonunitCorrelation
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootFourierNorm
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootBruhatL2
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootWeight

namespace OAI

/-! The exact projection norm is determined by the actual common unit
correlation and the literal local Gauss sum. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def cubicThetaPrimeCubeRootUnitCorrelation {p : Eisenstein} (hp : primaryPrime p)
    (u : cubicThetaAutomorphicL2) : ℂ :=
  inner ℂ (cubicThetaPrimeCubeRootWeylL2 hp (cubicThetaPrimeCubeRootLiftL2 hp u))
    (cubicThetaPrimeCubeRootLiftL2 hp (cubicThetaInversionMass u))

theorem cubicThetaPrimeCubeRoot_norm_gauss {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (u : cubicThetaAutomorphicL2) :
    (‖cubicThetaPrimeCubeRootFourierL2 hp (Ideal.Quotient.mk (modulus (p^3)) h)
      (cubicThetaPrimeCubeRootLiftL2 hp u)‖^2:ℂ)=
    (norm (p^3):ℂ)⁻¹*((‖u‖^2:ℂ)+cubicThetaPrimeCubeRootUnitCorrelation hp u*
      star (cubicThetaLocalPrimePowerGauss p hp.2.ne_zero 3 h)) := by
  classical
  let : Finite (Residues (p^3)) := finite_residues (pow_ne_zero 3 hp.2.ne_zero)
  let : Fintype (Residues (p^3)) := Fintype.ofFinite _
  let k := Ideal.Quotient.mk (modulus (p^3)) h
  let ψ := residueFourierChar (p^3) (pow_ne_zero 3 hp.2.ne_zero)
  let w := fun r : Residues (p^3) => cubicSymbol (p^3) (residueRepresentative (p^3) r)
  let C := cubicThetaPrimeCubeRootUnitCorrelation hp u
  have ht (r : Residues (p^3)) :
      star (ψ (k*r))*inner ℂ (cubicThetaPrimeCubeRootLiftL2 hp u)
        (cubicThetaPrimeCubeRootResidueL2 hp r (cubicThetaPrimeCubeRootLiftL2 hp u))=
      (if r=0 then (‖u‖^2:ℂ) else 0)+C*star (w r*ψ (k*r)) := by
    by_cases hr0 : r=0
    · subst r
      rw [cubicThetaPrimeCubeRootResidueL2_zero,
        inner_self_eq_norm_sq_to_K (𝕜:=ℂ) (cubicThetaPrimeCubeRootLiftL2 hp u),
        (cubicThetaPrimeCubeRootLiftL2 hp).norm_map]
      simp only [mul_zero,AddChar.map_zero_eq_one,star_one,one_mul,ite_true,w,
        cubicThetaPrimeCubeRoot_weight_zero hp,zero_mul,star_zero,mul_zero,add_zero]
      rfl
    · rw [ite_eq_right hr0]
      by_cases hr : IsUnit r
      · rw [cubicThetaPrimeCubeRoot_unit_residue_correlation hp r hr]
        change star (ψ (k*r))*C=0+C*star (w r*ψ (k*r))
        rw [show w r=1 from cubicThetaPrimeCubeRoot_weight_unit hp r hr,one_mul,zero_add,mul_comm]
      · rw [cubicThetaPrimeCubeRoot_nonunit_correlation_zero hp r hr hr0]
        change star (ψ (k*r))*0=0+C*star (w r*ψ (k*r))
        rw [show w r=0 from cubicThetaPrimeCubeRoot_weight_nonunit hp r hr,
          zero_mul,star_zero,mul_zero,mul_zero,add_zero]
  rw [cubicThetaPrimeCubeRootFourierL2_norm_correlation]
  change (norm (p^3):ℂ)⁻¹*(∑ r : Residues (p^3),star (ψ (k*r))*
    inner ℂ (cubicThetaPrimeCubeRootLiftL2 hp u)
      (cubicThetaPrimeCubeRootResidueL2 hp r (cubicThetaPrimeCubeRootLiftL2 hp u)))=_
  simp_rw [ht]
  rw [Finset.sum_add_distrib,←Finset.mul_sum,←star_sum]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  simp only [cubicThetaLocalPrimePowerGauss,tsum_fintype]
  rfl

end CubicFirstMoment

end

end OAI
