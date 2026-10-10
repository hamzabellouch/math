import OAI.NumberTheory.Jacobsthal.Harmonic.ComplexSquareScaling

namespace OAI

namespace Erdos970

section

open scoped ComplexConjugate
namespace ErdosComplexCurveFactors
open ErdosCriticalGeometry

noncomputable def realCoefficients (F : MV ℂ) : MV ℝ :=
  AddMonoidAlgebra.ofCoeff (Finsupp.mapRange Complex.re (by simp) (AddMonoidAlgebra.coeff F))

theorem coeff_realCoefficients (F : MV ℂ) (m : Fin 2 →₀ ℕ) :
    (realCoefficients F).coeff m = (F.coeff m).re := rfl

theorem complexify_realCoefficients (F : MV ℂ) (hF : conjugate F = F) :
    complexify (realCoefficients F) = F := by
  ext m
  change (MvPolynomial.map (algebraMap ℝ ℂ) (realCoefficients F)).coeff m = F.coeff m
  rw [MvPolynomial.coeff_map,coeff_realCoefficients]
  apply Complex.conj_eq_iff_re.mp
  have h := congrArg (fun P : MV ℂ => P.coeff m) hF
  simpa only [coeff_conjugate] using h

def RealScalable (F : MV ℂ) : Prop :=
  ∃ a : ℂ, a ≠ 0 ∧ ∃ R : MV ℝ, F = MvPolynomial.C a * complexify R

theorem normalized_conjugate_eq (F : MV ℂ) (c : ℂ) (hc : c ≠ 0)
    (hrel : conjugate F = MvPolynomial.C c * F) (m : Fin 2 →₀ ℕ)
    (hm : F.coeff m ≠ 0) :
    conjugate (MvPolynomial.C (F.coeff m)⁻¹ * F) = MvPolynomial.C (F.coeff m)⁻¹ * F := by
  have hcoeff (k : Fin 2 →₀ ℕ) : conj (F.coeff k) = c*F.coeff k := by
    have h := congrArg (fun P : MV ℂ => P.coeff k) hrel
    simpa only [coeff_conjugate,MvPolynomial.coeff_C_mul] using h
  ext k
  simp only [coeff_conjugate,MvPolynomial.coeff_C_mul,map_mul,map_inv₀,hcoeff]
  field_simp [hc,hm]

theorem realScalable_of_dvd_conjugate (F : MV ℂ) (hF : Irreducible F)
    (hdiv : F ∣ conjugate F) : RealScalable F := by
  obtain ⟨H,hH⟩ := hdiv
  have hu : IsUnit H := ((conjugate_irreducible hF).2 hH).resolve_left hF.not_isUnit
  obtain ⟨c,hc,hC⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hu
  have hc0 : c ≠ 0 := hc.ne_zero
  have hrel : conjugate F = MvPolynomial.C c * F := by rw [hH,hC,mul_comm]
  obtain ⟨m,hm⟩ := MvPolynomial.exists_coeff_ne_zero hF.ne_zero
  let N := MvPolynomial.C (F.coeff m)⁻¹ * F
  have hN : conjugate N = N := normalized_conjugate_eq F c hc0 hrel m hm
  have hR : complexify (realCoefficients N) = N := complexify_realCoefficients N hN
  refine ⟨F.coeff m,hm,realCoefficients N,?_⟩
  rw [hR]
  change F = MvPolynomial.C (F.coeff m) * (MvPolynomial.C (F.coeff m)⁻¹ * F)
  rw [← mul_assoc,← map_mul,mul_inv_cancel₀ hm,map_one,one_mul]

theorem nonreal_not_dvd_conjugate (F : MV ℂ) (hF : Irreducible F)
    (hreal : ¬RealScalable F) : ¬F ∣ conjugate F :=
  fun h => hreal (realScalable_of_dvd_conjugate F hF h)

end ErdosComplexCurveFactors

end

end Erdos970

end OAI
