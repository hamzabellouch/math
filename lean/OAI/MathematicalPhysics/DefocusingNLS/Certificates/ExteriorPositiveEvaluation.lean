import OAI.MathematicalPhysics.DefocusingNLS.Certificates.ExteriorCertificatePositivity
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.ExteriorRealProjection

namespace OAI

/-! Positive coefficient enclosures imply the actual exterior inequalities. -/

open Polynomial
namespace DefocusingNLS.ExteriorCertificate
open GaussianEnclosure

theorem positiveCoefficients_get {as : BoundaryCertificate.EnclosurePolynomial}
    (h : positiveCoefficients as = true) (n : ℕ) (hn : n < as.length) :
    (as[n]?.getD zero).error < (as[n]?.getD zero).center.re := by
  have ha : ∀ a ∈ as, a.error < a.center.re := by
    simpa only [positiveCoefficients,List.all_eq_true,decide_eq_true_eq] using h
  simpa only [List.getElem?_eq_getElem hn,Option.getD_some] using
    ha as[n] (List.getElem_mem hn)

private theorem eval_re_eq_sum (p : Polynomial ℂ) (N : ℕ)
    (hdeg : p.natDegree < N) (v : ℝ) :
    (p.eval (v : ℂ)).re = ∑ n ∈ Finset.range N, (p.coeff n).re*v^n := by
  conv_lhs => rw [p.as_sum_range' N hdeg]
  simp only [eval_finsetSum,eval_monomial,Complex.re_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im]
  ring

theorem positive_eval_of_positiveCoefficients
    (as : BoundaryCertificate.EnclosurePolynomial) (p : Polynomial ℂ) (N : ℕ)
    (hN : 0 < N) (hlen : as.length = N) (hpos : positiveCoefficients as = true)
    (hp : EnclosesPolynomial as p) (hdeg : p.natDegree < N)
    (v : ℝ) (hv : 0 ≤ v) : 0 < (p.eval (v : ℂ)).re := by
  have hc (n : ℕ) (hn : n < N) : 0 < (p.coeff n).re := by
    apply realPart_pos (coefficient_sound hp n)
    exact positiveCoefficients_get hpos n (by omega)
  rw [eval_re_eq_sum p N hdeg]
  apply Finset.sum_pos'
  · intro n hn
    exact mul_nonneg (hc n (Finset.mem_range.mp hn)).le (pow_nonneg hv n)
  · exact ⟨0,Finset.mem_range.mpr hN,by simpa using hc 0 hN⟩

end DefocusingNLS.ExteriorCertificate

end OAI
