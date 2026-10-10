import OAI.Probability.LatticePassage.FiniteVariance

namespace OAI

namespace CompanionFPP
open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
  (μ : Measure α) [IsProbabilityMeasure μ]

noncomputable def exchangeCoordinate (i : ι) (z : (ι → α) × (ι → α)) :
    (ι → α) × (ι → α) :=
  (Function.update z.1 i (z.2 i), Function.update z.2 i (z.1 i))

lemma exchangeCoordinate_preserving (i : ι) :
    MeasurePreserving (exchangeCoordinate i)
      ((Measure.pi (fun _ : ι => μ)).prod (Measure.pi (fun _ : ι => μ)))
      ((Measure.pi (fun _ : ι => μ)).prod (Measure.pi (fun _ : ι => μ))) := by
  have hA := measurePreserving_arrowProdEquivProdArrow α α ι (fun _ : ι => μ) (fun _ : ι => μ)
  let s := fun j : ι => if j = i then (Prod.swap : α × α → α × α) else id
  have hs : ∀ j, MeasurePreserving (s j) (μ.prod μ) (μ.prod μ) := by
    intro j
    by_cases hj : j = i
    · simpa [s, hj] using (Measure.measurePreserving_swap (μ := μ) (ν := μ))
    · simpa [s, hj] using (MeasurePreserving.id (μ.prod μ))
  have hp := measurePreserving_pi (fun _ : ι => μ.prod μ) (fun _ : ι => μ.prod μ) hs
  have h := hA.comp (hp.comp hA.symm)
  convert h using 1
  funext z
  apply Prod.ext <;> funext j <;>
    by_cases hj : j = i <;>
    simp [exchangeCoordinate, Function.comp_def, s, hj,
      MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow]

omit [Fintype ι] [MeasurableSpace α] in
lemma exchangeCoordinate_first (i : ι) (z : (ι → α) × (ι → α)) :
    (exchangeCoordinate i z).1 = Function.update z.1 i (z.2 i) := rfl

omit [Fintype ι] [MeasurableSpace α] in
lemma exchangeCoordinate_resample (i : ι) (z : (ι → α) × (ι → α)) :
    Function.update (exchangeCoordinate i z).1 i ((exchangeCoordinate i z).2 i) = z.1 := by
  simp [exchangeCoordinate]

theorem resampling_positive_negative_lintegral (f : (ι → α) → ℝ) (hf : Measurable f)
    (i : ι) (k : ℕ) :
    (∫⁻ z : (ι → α) × (ι → α),
      ENNReal.ofReal ((max (f (Function.update z.1 i (z.2 i)) - f z.1) 0)^k)
      ∂(Measure.pi (fun _ : ι => μ)).prod (Measure.pi (fun _ : ι => μ))) =
    (∫⁻ z : (ι → α) × (ι → α),
      ENNReal.ofReal ((max (f z.1 - f (Function.update z.1 i (z.2 i))) 0)^k)
      ∂(Measure.pi (fun _ : ι => μ)).prod (Measure.pi (fun _ : ι => μ))) := by
  let H := fun z : (ι → α) × (ι → α) =>
    ENNReal.ofReal ((max (f (Function.update z.1 i (z.2 i)) - f z.1) 0)^k)
  have hH : Measurable H := by dsimp [H]; fun_prop
  have he := lintegral_map (μ := (Measure.pi (fun _ : ι => μ)).prod (Measure.pi (fun _ : ι => μ))) hH (exchangeCoordinate_preserving μ i).measurable
  rw [(exchangeCoordinate_preserving μ i).map_eq] at he
  rw [he]
  apply lintegral_congr
  intro z
  dsimp [H]
  rw [exchangeCoordinate_resample, exchangeCoordinate_first]

lemma abs_sub_pow_split (a b : ℝ) (k : ℕ) (hk : 1 ≤ k) :
    |a-b|^k = (max (a-b) 0)^k + (max (b-a) 0)^k := by
  rcases le_total b a with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr h), max_eq_left (sub_nonneg.mpr h),
      max_eq_right (sub_nonpos.mpr h), zero_pow (by omega), add_zero]
  · rw [abs_of_nonpos (sub_nonpos.mpr h), max_eq_right (sub_nonpos.mpr h),
      max_eq_left (sub_nonneg.mpr h), zero_pow (by omega), zero_add, neg_sub]

theorem resampling_absolute_lintegral (f : (ι → α) → ℝ) (hf : Measurable f)
    (i : ι) (k : ℕ) (hk : 1 ≤ k) :
    (∫⁻ z : (ι → α) × (ι → α),
      ENNReal.ofReal (|f (Function.update z.1 i (z.2 i)) - f z.1|^k)
      ∂(Measure.pi (fun _ : ι => μ)).prod (Measure.pi (fun _ : ι => μ))) =
    2 * (∫⁻ z : (ι → α) × (ι → α),
      ENNReal.ofReal ((max (f (Function.update z.1 i (z.2 i)) - f z.1) 0)^k)
      ∂(Measure.pi (fun _ : ι => μ)).prod (Measure.pi (fun _ : ι => μ))) := by
  have he (a b : ℝ) : ENNReal.ofReal (|a-b|^k) =
      ENNReal.ofReal ((max (a-b) 0)^k) + ENNReal.ofReal ((max (b-a) 0)^k) := by
    rw [abs_sub_pow_split a b k hk, ENNReal.ofReal_add (by positivity) (by positivity)]
  simp_rw [he]
  rw [lintegral_add_left (by fun_prop),
    ← resampling_positive_negative_lintegral μ f hf i k, two_mul]

end CompanionFPP

end OAI
