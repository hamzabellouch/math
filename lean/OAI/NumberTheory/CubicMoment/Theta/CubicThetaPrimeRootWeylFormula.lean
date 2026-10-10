import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootWeylKernel
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootFourierResolution

namespace OAI

/-! The actual Fourier block of Weyl inversion is its explicit finite
Kloosterman scalar plus the retained zero/dilation branch. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace CubicFirstMoment

lemma cubicThetaPrimeRootWeylKernel_sum_erase {p : Eisenstein} (hp : primaryPrime p)
    [Fintype (Residues p)] (j k : Residues p) :
    (∑ r ∈ Finset.univ.erase (0:Residues p),
      star (residueFourierChar p hp.2.ne_zero (k*r))*cubicResidueChar p hp r*
        residueFourierChar p hp.2.ne_zero (-(j*cubicThetaPrimeRootReciprocal p r)))=
      cubicThetaPrimeRootWeylKernel hp j k := by
  let : (modulus p).IsPrime := (Ideal.span_singleton_prime hp.2.ne_zero).mpr hp.2
  rw [cubicThetaPrimeRootWeylKernel,tsum_fintype,
    ←Finset.sum_erase_add _ _ (Finset.mem_univ (0:Residues p))]
  simp only [mul_zero, AddChar.map_zero_eq_one, star_one,
    MulChar.map_zero, zero_mul, add_zero]

theorem cubicThetaPrimeRootWeyl_fourier_formula {p : Eisenstein} (hp : primaryPrime p)
    (j k : Residues p) (F : CubicThetaSection) :
    cubicThetaPrimeRootFourierProjection hp j (cubicThetaPrimeRootWeylSection hp
      (cubicThetaPrimeRootFourierProjection hp k (cubicThetaPrimeRootSectionRestrict F)))=
      (norm p:ℂ)⁻¹ •
        (cubicThetaPrimeRootFourierProjection hp j
          (cubicThetaPrimeRootWeylSection hp (cubicThetaPrimeRootSectionRestrict F))+
          (cubicSymbol p 3*cubicThetaPrimeRootWeylKernel hp j k) •
            cubicThetaPrimeRootFourierProjection hp j
              (cubicThetaPrimeRootSectionRestrict (cubicThetaInversionSection F))) := by
  classical
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Fintype (Residues p) := Fintype.ofFinite _
  let A := cubicThetaPrimeRootFourierProjection hp j
    (cubicThetaPrimeRootWeylSection hp (cubicThetaPrimeRootSectionRestrict F))
  let V := cubicThetaPrimeRootFourierProjection hp j
    (cubicThetaPrimeRootSectionRestrict (cubicThetaInversionSection F))
  rw [cubicThetaPrimeRootWeyl_fourier_row]
  apply congrArg (fun G : cubicThetaPrimeRootSections p => (norm p:ℂ)⁻¹ • (A+G))
  rw [←Finset.sum_smul]
  apply congrArg (fun c : ℂ => c • V)
  rw [←cubicThetaPrimeRootWeylKernel_sum_erase hp j k,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  ring

end CubicFirstMoment

end

end OAI
