import OAI.Analysis.HyperbolicCones.Hyperbolicity
import OAI.Analysis.HyperbolicCones.LineShift

namespace OAI

noncomputable section

namespace Paper256

theorem cone_iff_nonnegative_real_roots (x : Ambient) : x ∈ cone ↔
    ∀ t : ℝ, (linePolynomial x).eval t = 0 → 0 ≤ t := by
  constructor
  · intro hx t ht
    have hc : (linePolynomial x).aeval (t : ℂ) = 0 := by rw [real_aeval, ht]; rfl
    exact (hx (t : ℂ) hc).2
  · intro hx z hz
    have hi := linePolynomial_complex_roots_real x z hz
    refine ⟨hi, hx z.re ?_⟩
    have he : (z.re : ℂ) = z := by
      apply Complex.ext
      · rfl
      · simpa only [Complex.ofReal_im] using hi.symm
    have hr : Complex.ofReal ((linePolynomial x).eval z.re) = 0 := by
      rw [← real_aeval, he, hz]
    exact_mod_cast hr

theorem cone_iff_no_positive_shift (x : Ambient) : x ∈ cone ↔
    ∀ t : ℝ, 0 < t → MvPolynomial.eval (coordinates (x + t • basePoint)) polynomial ≠ 0 := by
  rw [cone_iff_nonnegative_real_roots]
  constructor
  · intro hx t ht he
    have h := hx (-t) ((linePolynomial_eval_neg x t).trans he)
    linarith
  · intro hx t ht
    by_contra hn
    have hpos : 0 < -t := by linarith
    apply hx (-t) hpos
    rw [← linePolynomial_eval_neg, neg_neg, ht]

end Paper256

end

end OAI
