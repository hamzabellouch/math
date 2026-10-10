import OAI.Analysis.KadisonKastler.DemodulatedPoisson
import OAI.Analysis.KadisonKastler.BoundaryErgodicReduction

namespace OAI

/-! # Quantitative estimates for the two analytic smoothing fields

Boundary products of two approximate unitary fields have quadratic error.
Once the Hardy product identity identifies their positive-height product
with its Poisson integral, positivity of that integral retains the error.
The product identity is a hypothesis of these estimates.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

section Product

variable {A : Type*} [NormedRing A]

theorem norm_product_sub_product_of_contractions
    (a b u v : A) {δ : ℝ} (hδ : 0 ≤ δ)
    (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (ha : ‖a - u‖ ≤ δ) (hb : ‖b - v‖ ≤ δ) :
    ‖a * b - u * v‖ ≤ 2 * δ + δ ^ 2 := by
  have han : ‖a‖ ≤ 1 + δ := by
    have h := norm_sub_le_norm_sub_add_norm_sub a u (0 : A)
    simp only [sub_zero] at h
    linarith
  have he : a * b - u * v = a * (b - v) + (a - u) * v := by
    rw [mul_sub, sub_mul]
    abel
  rw [he]
  calc
    _ ≤ ‖a * (b - v)‖ + ‖(a - u) * v‖ := norm_add_le _ _
    _ ≤ (1 + δ) * δ + δ * 1 := add_le_add
      ((norm_mul_le _ _).trans (mul_le_mul han hb (norm_nonneg _) (by positivity)))
      ((norm_mul_le _ _).trans (mul_le_mul ha hv (norm_nonneg _) hδ))
    _ = _ := by ring

end Product

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- A product field is measurable on every vector, even when it is not
measurable for the operator norm topology. -/
theorem operator_product_vector_measurable
    (B S : ℝ → H →L[ℂ] H)
    (hB : ∀ x, AEStronglyMeasurable (fun s => B s x) volume)
    (hS : ∀ x, AEStronglyMeasurable (fun s => S s x) volume) :
    ∀ x, AEStronglyMeasurable (fun s => (B s * S s) x) volume := by
  intro x
  exact aestronglyMeasurable_field_apply B hB (fun s => S s x) (hS x)

omit [CompleteSpace H] in
/-- Uniform contraction targets give an essential product error. -/
theorem ae_product_error
    (B S U V : ℝ → H →L[ℂ] H) {δ : ℝ} (hδ : 0 ≤ δ)
    (hU : ∀ᵐ s, ‖U s‖ ≤ 1) (hV : ∀ᵐ s, ‖V s‖ ≤ 1)
    (hB : ∀ᵐ s, ‖B s - U s‖ ≤ δ) (hS : ∀ᵐ s, ‖S s - V s‖ ≤ δ) :
    ∀ᵐ s, ‖B s * S s - U s * V s‖ ≤ 2 * δ + δ ^ 2 := by
  filter_upwards [hU, hV, hB, hS] with s hu hv hb hs
  exact norm_product_sub_product_of_contractions _ _ _ _ hδ hu hv hb hs

/-- Essential product bounds pass to every positive-height average. -/
theorem norm_poisson_product_error
    (B S U V : ℝ → H →L[ℂ] H)
    (hB : ∀ x, AEStronglyMeasurable (fun s => B s x) volume)
    (hS : ∀ x, AEStronglyMeasurable (fun s => S s x) volume)
    (hU : ∀ x, AEStronglyMeasurable (fun s => U s x) volume)
    (hV : ∀ x, AEStronglyMeasurable (fun s => V s x) volume)
    {CB CS : ℝ} (hb : ∀ᵐ s, ‖B s‖ ≤ CB) (hs : ∀ᵐ s, ‖S s‖ ≤ CS)
    (hCB : 0 ≤ CB)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hu : ∀ᵐ s, ‖U s‖ ≤ 1) (hv : ∀ᵐ s, ‖V s‖ ≤ 1)
    (hBU : ∀ᵐ s, ‖B s - U s‖ ≤ δ) (hSV : ∀ᵐ s, ‖S s - V s‖ ≤ δ)
    (t r : ℝ) (hr : 0 < r) :
    ∃ (hBS : ∀ᵐ s, ‖B s * S s‖ ≤ CB * CS)
      (hUV : ∀ᵐ s, ‖U s * V s‖ ≤ 1),
    ‖measurablePoissonAverage (fun s => B s * S s)
        (operator_product_vector_measurable B S hB hS) (CB * CS) hBS t r hr -
      measurablePoissonAverage (fun s => U s * V s)
        (operator_product_vector_measurable U V hU hV) 1 hUV t r hr‖ ≤ 2 * δ + δ ^ 2 := by
  have hBS : ∀ᵐ s, ‖B s * S s‖ ≤ CB * CS := by
    filter_upwards [hb, hs] with s hb hs
    exact (norm_mul_le _ _).trans (mul_le_mul hb hs (norm_nonneg _) hCB)
  have hUV : ∀ᵐ s, ‖U s * V s‖ ≤ 1 := by
    filter_upwards [hu, hv] with s hu hv
    exact (norm_mul_le _ _).trans ((mul_le_mul hu hv (norm_nonneg _) (by norm_num)).trans_eq
      (by norm_num))
  exact ⟨hBS, hUV, norm_measurablePoissonAverage_sub_le _ _ _ _ _ _ hBS hUV
    (by positivity) (ae_product_error B S U V hδ hu hv hBU hSV) t r hr⟩

/-- The explicit demodulation factor grows at most linearly at small height. -/
theorem exp_mul_one_add_le {r δ : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    Real.exp r * (1 + δ) ≤ 1 + 4 * r + δ := by
  have he := Real.abs_exp_sub_one_le (x := r) (by simpa [abs_of_nonneg hr] using hr1)
  have he' : Real.exp r ≤ 1 + 2 * r := by
    rw [abs_of_nonneg hr] at he
    linarith [le_abs_self (Real.exp r - 1)]
  calc
    Real.exp r * (1 + δ) ≤ (1 + 2 * r) * (1 + δ) :=
      mul_le_mul_of_nonneg_right he' (by positivity)
    _ ≤ 1 + 4 * r + δ := by nlinarith

omit [CompleteSpace H] in
/-- The constructed Poisson smoothing has an absolute first-order norm bound. -/
theorem norm_demodulatedPoissonAverage_le_small
    (B : ℝ → H →L[ℂ] H)
    (hB : ∀ x, AEStronglyMeasurable (fun s => B s x) volume)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hb : ∀ᵐ s, ‖B s‖ ≤ 1 + δ) (t r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    ‖demodulatedPoissonAverage B hB (1 + δ) hb t r hr‖ ≤ 1 + 4 * r + δ :=
  (norm_demodulatedPoissonAverage_le B hB (by positivity) hb t r hr).trans
    (exp_mul_one_add_le hr.le hr1 hδ hδ1)

end

end KadisonKastler

end OAI
