import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

namespace OAI

/-! The Hilbert-space variance estimate for geodesic averages. Applying this
to the Jacobi curvature matrix in the Hilbert space of square-integrable
fields separates the averaging argument from the geometric flow identities. -/

namespace PositiveEinsteinFour.Averages

open MeasureTheory Filter

noncomputable section

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → E}

omit [CompleteSpace E] in
theorem integrable_sq_distance (hf : Integrable f μ)
    (hf2 : Integrable (fun t => ‖f t‖ ^ 2) μ) (a : E) :
    Integrable (fun t => ‖a - f t‖ ^ 2) μ := by
  have h := ((integrable_const (‖a‖ ^ 2)).sub ((hf.const_inner a).const_mul 2)).add hf2
  convert h using 1
  ext t
  exact norm_sub_sq_real a (f t)

theorem integral_sq_distance (hf : Integrable f μ)
    (hf2 : Integrable (fun t => ‖f t‖ ^ 2) μ) (a : E) :
    (∫ t, ‖a - f t‖ ^ 2 ∂μ) =
      ‖a‖ ^ 2 - 2 * inner ℝ a (∫ t, f t ∂μ) + ∫ t, ‖f t‖ ^ 2 ∂μ := by
  simp_rw [norm_sub_sq_real]
  have hadd := integral_add ((integrable_const (‖a‖ ^ 2)).sub
    ((hf.const_inner a).const_mul 2)) hf2
  have hsub := integral_sub (integrable_const (‖a‖ ^ 2))
    ((hf.const_inner a).const_mul 2)
  simp only [Pi.sub_apply] at hadd hsub
  rw [hadd, hsub, integral_const_mul, integral_inner hf a]
  simp only [integral_const, probReal_univ, one_smul]

theorem integrable_mean_sq_distance (hf : Integrable f μ)
    (hf2 : Integrable (fun t => ‖f t‖ ^ 2) μ) :
    Integrable (fun s => ∫ t, ‖f s - f t‖ ^ 2 ∂μ) μ := by
  have h := (hf2.sub ((hf.inner_const (∫ t, f t ∂μ)).const_mul 2)).add
    (integrable_const (∫ t, ‖f t‖ ^ 2 ∂μ))
  convert h using 1
  ext s
  exact integral_sq_distance hf hf2 (f s)

/-- The double-variance identity, with only the integrability needed by the
application. The two integrals need not be interchanged. -/
theorem double_variance_identity (hf : Integrable f μ)
    (hf2 : Integrable (fun t => ‖f t‖ ^ 2) μ) :
    (∫ s, ∫ t, ‖f s - f t‖ ^ 2 ∂μ ∂μ) =
      2 * ((∫ t, ‖f t‖ ^ 2 ∂μ) - ‖∫ t, f t ∂μ‖ ^ 2) := by
  simp_rw [integral_sq_distance hf hf2]
  have hadd := integral_add (hf2.sub ((hf.inner_const (∫ t, f t ∂μ)).const_mul 2))
    (integrable_const (∫ t, ‖f t‖ ^ 2 ∂μ))
  have hsub := integral_sub hf2 ((hf.inner_const (∫ t, f t ∂μ)).const_mul 2)
  simp only [Pi.sub_apply] at hadd hsub
  rw [hadd, hsub, integral_const_mul]
  have hinner : (∫ s, inner ℝ (f s) (∫ t, f t ∂μ) ∂μ) = ‖∫ t, f t ∂μ‖ ^ 2 := by
    calc
      _ = ∫ s, inner ℝ (∫ t, f t ∂μ) (f s) ∂μ := by
        apply integral_congr_ae
        exact Eventually.of_forall fun s => real_inner_comm _ _
      _ = inner ℝ (∫ t, f t ∂μ) (∫ t, f t ∂μ) := integral_inner hf _
      _ = _ := real_inner_self_eq_norm_sq _
  rw [hinner]
  simp only [integral_const, probReal_univ, one_smul]
  ring

/-- A stationary Hilbert-valued curve with a mean-square increment bound
retains this much squared norm after averaging. In the geodesic application,
`L` is the averaged squared norm of the directional derivative. -/
theorem stationary_average_lower {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {A : ℝ → E} {q L : ℝ}
    (hA : Integrable A ν) (hA2 : Integrable (fun t => ‖A t‖ ^ 2) ν)
    (ht : Integrable (fun t : ℝ => t) ν)
    (ht2 : Integrable (fun t : ℝ => t ^ 2) ν)
    (hstationary : ∀ᵐ t ∂ν, ‖A t‖ ^ 2 = q)
    (hincrement : ∀ s t, ‖A s - A t‖ ^ 2 ≤ L * (s - t) ^ 2) :
    q - L * ((∫ t, t ^ 2 ∂ν) - (∫ t, t ∂ν) ^ 2) ≤ ‖∫ t, A t ∂ν‖ ^ 2 := by
  have ht2' : Integrable (fun t : ℝ => ‖t‖ ^ 2) ν := by simpa using ht2
  have hpoint (s : ℝ) : (∫ t, ‖A s - A t‖ ^ 2 ∂ν) ≤
      L * ∫ t, ‖s - t‖ ^ 2 ∂ν := by
    calc
      _ ≤ ∫ t, L * ‖s - t‖ ^ 2 ∂ν := by
        apply integral_mono (integrable_sq_distance hA hA2 (A s))
          ((integrable_sq_distance ht ht2' s).const_mul L)
        intro t
        simpa using hincrement s t
      _ = _ := integral_const_mul _ _
  have hbound := integral_mono (integrable_mean_sq_distance hA hA2)
    ((integrable_mean_sq_distance ht ht2').const_mul L) hpoint
  rw [double_variance_identity hA hA2, integral_const_mul,
    double_variance_identity ht ht2'] at hbound
  have hq : (∫ t, ‖A t‖ ^ 2 ∂ν) = q := by
    rw [integral_congr_ae hstationary]
    simp
  rw [hq] at hbound
  simp only [Real.norm_eq_abs, sq_abs] at hbound
  linarith

omit [CompleteSpace E] in
/-- An invariant averaged derivative bound controls increments of the
Hilbert-valued curvature curve. This is also valid for an `L²` Hilbert space. -/
theorem increment_bound_of_derivative {A d : ℝ → E} {L : ℝ} (hL : 0 ≤ L)
    (hd : ∀ t, HasDerivAt A (d t) t) (hbound : ∀ t, ‖d t‖ ^ 2 ≤ L) (s t : ℝ) :
    ‖A s - A t‖ ^ 2 ≤ L * (s - t) ^ 2 := by
  have hnorm (z : ℝ) : ‖d z‖ ≤ Real.sqrt L := by
    nlinarith [hbound z, Real.sqrt_nonneg L, Real.sq_sqrt hL, norm_nonneg (d z)]
  have hforward (a b : ℝ) (hab : a ≤ b) :
      ‖A b - A a‖ ≤ Real.sqrt L * (b - a) := by
    exact norm_image_sub_le_of_norm_deriv_le_segment'
      (fun z _ => (hd z).hasDerivWithinAt) (fun z _ => hnorm z) b ⟨hab, le_rfl⟩
  have hdist : ‖A s - A t‖ ≤ Real.sqrt L * |s - t| := by
    rcases le_total t s with hts | hst
    · simpa only [abs_of_nonneg (sub_nonneg.mpr hts)] using hforward t s hts
    · rw [norm_sub_rev, abs_of_nonpos (sub_nonpos.mpr hst), neg_sub]
      exact hforward s t hst
  have hsq := mul_le_mul hdist hdist (norm_nonneg _) (by positivity)
  simpa only [← pow_two, mul_pow, Real.sq_sqrt hL, sq_abs] using hsq

end

end PositiveEinsteinFour.Averages

end OAI
