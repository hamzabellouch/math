import Mathlib
import OAI.Analysis.Commutator.MinimalProjection

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace Kadison.AtomicFactor

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma corner_scalar (M : VonNeumannAlgebra H) {p : H →L[ℂ] H}
    (hp : IsMinimalProjection M p) {a : H →L[ℂ] H} (haM : a∈M)
    (hpa : p*a=a) (hap : a*p=a) : ∃ z : ℂ,a=z • p := by
  have hps : p*star a=star a := by
    simpa only [star_mul,hp.2.1.isSelfAdjoint.star_eq] using congrArg star hap
  have hsp : star a*p=star a := by
    simpa only [star_mul,hp.2.1.isSelfAdjoint.star_eq] using congrArg star hpa
  let ar : H →L[ℂ] H := realPart a
  let ai : H →L[ℂ] H := imaginaryPart a
  have hrM : ar∈M := by
    rw [show ar=(2:ℝ)⁻¹ • (a+star a) from realPart_apply_coe a]
    exact (M.toSubalgebra.restrictScalars ℝ).smul_mem (M.add_mem haM (M.star_mem' haM)) _
  have hiM : ai∈M := by
    rw [show ai= -Complex.I • (2:ℝ)⁻¹ • (a-star a) from imaginaryPart_apply_coe a]
    exact M.smul_mem ((M.toSubalgebra.restrictScalars ℝ).smul_mem (M.sub_mem haM (M.star_mem' haM)) _) _
  have hpr : p*ar=ar := by
    simp only [ar,realPart_apply_coe,mul_smul_comm,mul_add,hpa,hps]
  have hrp : ar*p=ar := by
    simp only [ar,realPart_apply_coe,smul_mul_assoc,add_mul,hap,hsp]
  have hpi : p*ai=ai := by
    simp only [ai,imaginaryPart_apply_coe,mul_smul_comm,mul_sub,hpa,hps]
  have hip : ai*p=ai := by
    simp only [ai,imaginaryPart_apply_coe,smul_mul_assoc,sub_mul,hap,hsp]
  obtain ⟨r,hr⟩ := selfadjoint_corner_scalar M hp hrM (realPart a).property hpr hrp
  obtain ⟨s,hs⟩ := selfadjoint_corner_scalar M hp hiM (imaginaryPart a).property hpi hip
  refine ⟨r+Complex.I*s,?_⟩
  calc
    a=ar+Complex.I • ai := (realPart_add_I_smul_imaginaryPart a).symm
    _=(r+Complex.I*s) • p := by rw [hr,hs,smul_smul,add_smul]

end Kadison.AtomicFactor

end

end
end

end OAI
