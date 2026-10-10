import OAI.MathematicalPhysics.DefocusingNLS.Certificates.ExteriorLeadingCoefficient
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.ExteriorRealProjection

namespace OAI

/-! The highest off-diagonal coefficient is real for the entire parameter family. -/

open Polynomial Matrix
namespace DefocusingNLS.ExteriorCertificate
open BoundaryCertificate (stateMatrix)

attribute [local irreducible] polynomialState

theorem form_top_imaginary_zero (z₀ : ℤ) (b : ℝ) :
    ((formPolynomial z₀ b 1 0).coeff 9).im = 0 := by
  let T := stateMatrix (polynomialState z₀ b 5)
  let P := stateMatrix (polynomialState z₀ b 4)
  let d : ℂ := (((100000000*4 : ℤ) : ℂ)-Complex.I*(100000000*b : ℝ))-500000000
  let E : Polynomial ℂ := C d*conjugatePolynomial (T 0 1)*P 1 0-
    C (star d)*conjugatePolynomial (P 1 1)*T 0 0
  have hd : inputT 4 b-C (500000000 : ℂ) = C d := by
    simp only [inputT,d,map_sub]
    norm_num
  have hform : formPolynomial z₀ b 1 0 =
      C (500000000 : ℂ)*(conjugatePolynomial (T 0 1)*T 0 0)+inputS z₀*E := by
    rw [form_last_row]
    rw [hd]
    simp only [conjugatePolynomial,Polynomial.map_C,starRingEnd_apply]
    dsimp only [E,T,P]
    simp only [conjugatePolynomial]
    ring
  have hT (i j : Fin 2) : (T i j).natDegree ≤ 4+j.val := state_column_degree z₀ b 4 i j
  have hP (i j : Fin 2) : (P i j).natDegree ≤ 3+j.val := state_column_degree z₀ b 3 i j
  have hA : (conjugatePolynomial (T 0 1)*P 1 0).natDegree ≤ 8 :=
    natDegree_mul_le.trans (add_le_add ((conjugatePolynomial_degree _).trans (hT 0 1)) (hP 1 0))
  have hB : (conjugatePolynomial (P 1 1)*T 0 0).natDegree ≤ 8 :=
    natDegree_mul_le.trans (add_le_add ((conjugatePolynomial_degree _).trans (hP 1 1)) (hT 0 0))
  have hE : E.natDegree ≤ 8 := by
    dsimp only [E]
    rw [mul_assoc,mul_assoc]
    exact (natDegree_sub_le _ _).trans (max_le
      ((natDegree_C_mul_le d _).trans hA)
      ((natDegree_C_mul_le (star d) _).trans hB))
  have hE9 : E.coeff 9 = 0 := coeff_eq_zero_of_natDegree_lt (hE.trans_lt (by decide))
  have hF9 : (conjugatePolynomial (T 0 1)*T 0 0).coeff 9 =
      star ((T 0 1).coeff 5)*(T 0 0).coeff 4 := by
    simpa only [coeff_conjugatePolynomial] using
      (coeff_mul_add_eq_of_natDegree_le
        (show (conjugatePolynomial (T 0 1)).natDegree ≤ 5 from
          (conjugatePolynomial_degree _).trans (hT 0 1))
        (show (T 0 0).natDegree ≤ 4 from hT 0 0))
  have hA8 : (conjugatePolynomial (T 0 1)*P 1 0).coeff 8 =
      star ((T 0 1).coeff 5)*(P 1 0).coeff 3 := by
    simpa only [coeff_conjugatePolynomial] using
      (coeff_mul_add_eq_of_natDegree_le
        (show (conjugatePolynomial (T 0 1)).natDegree ≤ 5 from
          (conjugatePolynomial_degree _).trans (hT 0 1))
        (show (P 1 0).natDegree ≤ 3 from hP 1 0))
  have hB8 : (conjugatePolynomial (P 1 1)*T 0 0).coeff 8 =
      star ((P 1 1).coeff 4)*(T 0 0).coeff 4 := by
    simpa only [coeff_conjugatePolynomial] using
      (coeff_mul_add_eq_of_natDegree_le
        (show (conjugatePolynomial (P 1 1)).natDegree ≤ 4 from
          (conjugatePolynomial_degree _).trans (hP 1 1))
        (show (T 0 0).natDegree ≤ 4 from hT 0 0))
  have hE8 : E.coeff 8 = d*(star ((T 0 1).coeff 5)*(P 1 0).coeff 3)-
      star d*(star ((P 1 1).coeff 4)*(T 0 0).coeff 4) := by
    simp only [E,mul_assoc,coeff_sub,coeff_C_mul,hA8,hB8]
  have ht₁ := (state_leading z₀ b 4 1).1
  have ht₀ := (state_leading z₀ b 4 0).1
  have hp₀ := (state_leading z₀ b 3 0).2
  have hp₁ := (state_leading z₀ b 3 1).2
  change (T 0 1).coeff 5 = _ at ht₁
  change (T 0 0).coeff 4 = _ at ht₀
  change (P 1 0).coeff 3 = _ at hp₀
  change (P 1 1).coeff 4 = _ at hp₁
  rw [hform,coeff_add,coeff_C_mul,coeff_inputS_mul,hE9,mul_zero,zero_add,hF9,hE8,
    ht₁,ht₀,hp₀,hp₁]
  norm_num [firstLeading,d,pow_succ,Complex.mul_re,Complex.mul_im]
  ring

theorem imaginary_form_degree (z₀ : ℤ) (b : ℝ) :
    (negImagProjection (formPolynomial z₀ b 1 0)).natDegree ≤ 8 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [coeff_negImagProjection]
  by_cases h : n=9
  · subst n
    simp only [form_top_imaginary_zero,neg_zero,Complex.ofReal_zero]
  · have hz : (formPolynomial z₀ b 1 0).coeff n = 0 :=
      coeff_eq_zero_of_natDegree_lt ((form_degree z₀ b 0).trans_lt (by simp; omega))
    simp [hz]

end DefocusingNLS.ExteriorCertificate

end OAI
