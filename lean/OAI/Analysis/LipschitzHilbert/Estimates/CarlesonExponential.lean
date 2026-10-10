import OAI.Analysis.LipschitzHilbert.Estimates.LaminarCarleson
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Exponential

namespace OAI

/-!
# From factorial counting moments to an exponential tail

For a finite count the exponential series can be integrated using a
constant summable majorant. The exact factorial moment bound therefore
gives exponential average at most two and the required Markov tail.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

variable {X : Type*} [MeasurableSpace X]

attribute [local instance] Classical.propDecidable

theorem factorial_moments_exponential_bound (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → ℝ) (hf : Measurable f) {A B : ℝ} (hA : 0 < A) (hB : 0 ≤ B)
    (hf0 : ∀ x, 0 ≤ f x) (hfB : ∀ x, f x ≤ B)
    (hmoment : ∀ n : ℕ, (∫ x, f x ^ n ∂μ) ≤ (n.factorial : ℝ) * A ^ n * μ.real Set.univ) :
    Integrable (fun x => Real.exp (f x / (2 * A))) μ ∧
      (∫ x, Real.exp (f x / (2 * A)) ∂μ) ≤ 2 * μ.real Set.univ := by
  let F : ℕ → X → ℝ := fun n x => (f x / (2 * A)) ^ n / (n.factorial : ℝ)
  let bound : ℕ → ℝ := fun n => (B / (2 * A)) ^ n / (n.factorial : ℝ)
  have hden : 0 < 2 * A := by positivity
  have hbound0 : ∀ n, 0 ≤ bound n := fun n => by dsimp [bound]; positivity
  have hFbound (n : ℕ) (x : X) : ‖F n x‖ ≤ bound n := by
    have hfx0 := hf0 x
    have hF0 : 0 ≤ F n x := by dsimp [F]; positivity
    rw [Real.norm_of_nonneg hF0]
    dsimp [F, bound]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact pow_le_pow_left₀ (div_nonneg hfx0 hden.le)
      (div_le_div_of_nonneg_right (hfB x) hden.le) n
  have hFb (n : ℕ) : AEStronglyMeasurable (F n) μ := by
    exact ((hf.div_const _).pow_const n |>.div_const _).aestronglyMeasurable
  have hsum_bound : Summable bound := NormedSpace.expSeries_div_summable _
  have hseries (x : X) : HasSum (fun n => F n x) (Real.exp (f x / (2 * A))) := by
    simpa only [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp (f x / (2 * A))
  have hsum := hasSum_integral_of_dominated_convergence (μ := μ)
    (fun n _ => bound n) hFb (fun n => Filter.Eventually.of_forall (hFbound n))
    (Filter.Eventually.of_forall fun _ => hsum_bound) (integrable_const _)
    (Filter.Eventually.of_forall hseries)
  have hint : Integrable (fun x => Real.exp (f x / (2 * A))) μ := by
    apply Integrable.of_bound ((hf.div_const _).exp.aestronglyMeasurable)
      (Real.exp (B / (2 * A)))
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    apply Real.exp_le_exp.mpr
    exact div_le_div_of_nonneg_right (hfB x) hden.le
  have hterm (n : ℕ) : (∫ x, F n x ∂μ) ≤ (1 / 2 : ℝ) ^ n * μ.real Set.univ := by
    have hfact : 0 < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
    have hFn : F n = fun x => f x ^ n / ((2 * A) ^ n * (n.factorial : ℝ)) := by
      funext x
      dsimp [F]
      rw [div_pow, div_div]
    rw [hFn, integral_div]
    apply (div_le_iff₀ (mul_pos (pow_pos hden n) hfact)).2
    convert hmoment n using 1
    rw [mul_pow, div_pow]
    field_simp
    ring
  have hgeom : HasSum (fun n : ℕ => (1 / 2 : ℝ) ^ n * μ.real Set.univ)
      (2 * μ.real Set.univ) := by
    convert (hasSum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_right
      (μ.real Set.univ) using 1
    norm_num
  refine ⟨hint, ?_⟩
  rw [← hsum.tsum_eq, ← hgeom.tsum_eq]
  exact Summable.tsum_le_tsum hterm hsum.summable hgeom.summable

theorem exponential_moment_tail (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → ℝ) {A : ℝ} (hA : 0 < A)
    (hint : Integrable (fun x => Real.exp (f x / (2 * A))) μ)
    (haverage : (∫ x, Real.exp (f x / (2 * A)) ∂μ) ≤ 2 * μ.real Set.univ)
    (lambda : ℝ) :
    μ.real {x | lambda < f x} ≤ 2 * μ.real Set.univ * Real.exp (-lambda / (2 * A)) := by
  have hden : 0 < 2 * A := by positivity
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun x => (Real.exp_pos (f x / (2 * A))).le)
    hint (Real.exp (lambda / (2 * A)))
  have hsubset : {x | lambda < f x} ⊆
      {x | Real.exp (lambda / (2 * A)) ≤ Real.exp (f x / (2 * A))} := by
    intro x hx
    exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hx.le hden.le)
  have hmono := measureReal_mono (μ := μ) hsubset
  have hle : μ.real {x | lambda < f x} ≤
      (2 * μ.real Set.univ) / Real.exp (lambda / (2 * A)) := by
    apply (le_div_iff₀ (Real.exp_pos _)).2
    nlinarith [mul_le_mul_of_nonneg_left hmono (Real.exp_pos (lambda / (2 * A))).le]
  convert hle using 1
  simp only [div_eq_mul_inv, neg_mul, Real.exp_neg]

/-- Exact exponential tail for the finite occurrence count in one root. -/
theorem laminar_count_exponential_tail {ι : Type*} [Fintype ι]
    (Q : ι → Set X) (μ : Measure X) (rank : ι → ℤ)
    (hQ : ∀ i, MeasurableSet (Q i)) {P₀ : Set X} (hPfinite : μ P₀ ≠ ⊤)
    (hsub : ∀ i, Q i ⊆ P₀)
    (horder : ∀ i j, rank j ≤ rank i → (Q i ∩ Q j).Nonempty → Q j ⊆ Q i)
    {A : ℝ} (hA : 0 < A)
    (hcarleson : ∀ P, P = P₀ ∨ P ∈ Set.range Q →
      (∑ i, if Q i ⊆ P then μ.real (Q i) else 0) ≤ A * μ.real P)
    (lambda : ℝ) :
    μ.real ({x | lambda < laminarCount Q x} ∩ P₀) ≤
      2 * μ.real P₀ * Real.exp (-lambda / (2 * A)) := by
  have : IsFiniteMeasure (μ.restrict P₀) := isFiniteMeasure_restrict.mpr hPfinite
  have hm (n : ℕ) : (∫ x, laminarCount Q x ^ n ∂μ.restrict P₀) ≤
      (n.factorial : ℝ) * A ^ n * (μ.restrict P₀).real Set.univ := by
    simpa only [measureReal_restrict_apply_univ] using
      laminar_count_moment Q μ rank hQ hPfinite hsub horder hA.le hcarleson n
  obtain ⟨hint, haverage⟩ := factorial_moments_exponential_bound (μ.restrict P₀)
    (laminarCount Q) (measurable_laminarCount Q hQ) hA
    (Nat.cast_nonneg (Fintype.card ι)) (laminarCount_nonneg Q) (laminarCount_le_card Q) hm
  have htail := exponential_moment_tail (μ.restrict P₀) (laminarCount Q) hA hint haverage lambda
  simpa only [measureReal_restrict_apply (measurableSet_lt measurable_const
    (measurable_laminarCount Q hQ)), measureReal_restrict_apply_univ] using htail

end LipschitzHilbert

end

end OAI
