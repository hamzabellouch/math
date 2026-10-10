import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootFourierProducts

namespace OAI

/-! Exact Fourier matrix row of the actual conjugated inversion on a
global section. Its zero branch is retained separately from the finite
cubic-character row. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace CubicFirstMoment

theorem cubicThetaPrimeRootWeyl_fourier_row {p : Eisenstein} (hp : primaryPrime p)
    [Fintype (Residues p)] (j k : Residues p) (F : CubicThetaSection) :
    cubicThetaPrimeRootFourierProjection hp j (cubicThetaPrimeRootWeylSection hp
      (cubicThetaPrimeRootFourierProjection hp k (cubicThetaPrimeRootSectionRestrict F)))=
      (norm p:ℂ)⁻¹ •
        (cubicThetaPrimeRootFourierProjection hp j
          (cubicThetaPrimeRootWeylSection hp (cubicThetaPrimeRootSectionRestrict F))+
          ∑ r ∈ Finset.univ.erase (0:Residues p),
            (cubicSymbol p 3*star (residueFourierChar p hp.2.ne_zero (k*r))*cubicResidueChar p hp r*
              residueFourierChar p hp.2.ne_zero (-(j*cubicThetaPrimeRootReciprocal p r))) •
              cubicThetaPrimeRootFourierProjection hp j
                (cubicThetaPrimeRootSectionRestrict (cubicThetaInversionSection F))) := by
  classical
  let : (modulus p).IsPrime := (Ideal.span_singleton_prime hp.2.ne_zero).mpr hp.2
  let : Field (Residues p) := Fintype.fieldOfDomain _
  let RF := cubicThetaPrimeRootSectionRestrict (p:=p) F
  let IF := cubicThetaPrimeRootSectionRestrict (p:=p) (cubicThetaInversionSection F)
  let L : cubicThetaPrimeRootSections p →ₗ[ℂ] cubicThetaPrimeRootSections p :=
    (cubicThetaPrimeRootFourierProjection hp j).comp (cubicThetaPrimeRootWeylOperator hp).toLinearMap
  let ψ := residueFourierChar p hp.2.ne_zero
  have hn (r : Residues p) (hr : r≠0) :
      star (ψ (k*r)) • L (cubicThetaPrimeRootResidueOperator hp r RF)=
        (cubicSymbol p 3*star (ψ (k*r))*cubicResidueChar p hp r*
          ψ (-(j*cubicThetaPrimeRootReciprocal p r))) • cubicThetaPrimeRootFourierProjection hp j IF := by
    have he : L (cubicThetaPrimeRootResidueOperator hp r RF)=
        ((cubicSymbol p 3*cubicResidueChar p hp r)*ψ (-(j*cubicThetaPrimeRootReciprocal p r))) •
          cubicThetaPrimeRootFourierProjection hp j IF := by
      change cubicThetaPrimeRootFourierProjection hp j (cubicThetaPrimeRootWeylSection hp
        (cubicThetaPrimeRootResidueOperator hp r (cubicThetaPrimeRootSectionRestrict F)))=_
      rw [cubicThetaPrimeRootWeyl_residue_branch hp r (isUnit_iff_ne_zero.mpr hr),map_smul,
        cubicThetaPrimeRootFourierProjection_translate,mul_neg,smul_smul]
    rw [he,smul_smul]
    congr 1
    ring
  change L (cubicThetaPrimeRootFourierProjection hp k RF)=_
  rw [cubicThetaPrimeRootFourierProjection_apply,map_smul,map_sum]
  simp only [map_smul]
  rw [←Finset.sum_erase_add _ _ (Finset.mem_univ (0:Residues p))]
  simp only [mul_zero,AddChar.map_zero_eq_one,star_one,one_smul,
    cubicThetaPrimeRootResidueOperator_zero]
  rw [add_comm]
  congr 2
  apply Finset.sum_congr rfl
  intro r hr
  exact hn r (Finset.ne_of_mem_erase hr)

end CubicFirstMoment

end

end OAI
