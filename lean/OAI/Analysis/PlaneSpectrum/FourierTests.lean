import OAI.Analysis.PlaneSpectrum.Multipliers

namespace OAI

noncomputable section
open scoped ComplexConjugate
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
noncomputable section
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate

namespace PlaneFiveColor.InvariantMean
open scoped BigOperators
open MeasureTheory Filter Topology

lemma integralReal_congr (f g : AF → ℝ) {N M : ℕ} {B C : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → f t = 0)
    (hb : ∀ t, ‖f t‖ ≤ B)
    (gs : ∀ t : AF, (M : ℝ) < |(t : ℝ)| → g t = 0)
    (gb : ∀ t, ‖g t‖ ≤ C) (he : ∀ t, f t = g t) :
    integralReal f hs hb = integralReal g gs gb := by
  unfold integralReal
  congr 1
  ext x
  induction x using QuotientAddGroup.induction_on with
  | H t => simp only [periodBCF_mk, periodSum, he]

lemma integralReal_mul (f : AF → ℝ) (c : ℝ) {N M : ℕ} {B C : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → f t = 0)
    (hb : ∀ t, ‖f t‖ ≤ B)
    (gs : ∀ t : AF, (M : ℝ) < |(t : ℝ)| → c*f t = 0)
    (gb : ∀ t, ‖c*f t‖ ≤ C) :
    integralReal (fun t => c*f t) gs gb = c * integralReal f hs hb := by
  have he : periodBCF (fun t => c*f t) gs gb = c • periodBCF f hs hb := by
    ext x
    induction x using QuotientAddGroup.induction_on with
    | H t =>
      change (∑' k : ℤ, c * f (t+k)) = c * (∑' k : ℤ, f (t+k))
      exact tsum_mul_left
  exact (congrArg mean he).trans (mean_smul _ _)

lemma integralReal_sum {ι : Type*} (s : Finset ι) (f : ι → AF → ℝ)
    {N M : ℕ} {B : ι → ℝ} {C : ℝ}
    (hs : ∀ i, ∀ t : AF, (N : ℝ) < |(t : ℝ)| → f i t = 0)
    (hb : ∀ i t, ‖f i t‖ ≤ B i)
    (gs : ∀ t : AF, (M : ℝ) < |(t : ℝ)| → (∑ i ∈ s, f i t) = 0)
    (gb : ∀ t, ‖∑ i ∈ s, f i t‖ ≤ C) :
    integralReal (fun t => ∑ i ∈ s, f i t) gs gb =
      ∑ i ∈ s, integralReal (f i) (hs i) (hb i) := by
  have he : periodBCF (fun t => ∑ i ∈ s, f i t) gs gb =
      ∑ i ∈ s, periodBCF (f i) (hs i) (hb i) := by
    ext x
    rw [BoundedContinuousFunction.sum_apply]
    induction x using QuotientAddGroup.induction_on with
    | H t =>
      simp only [periodBCF_mk, periodSum]
      exact Summable.tsum_finsetSum (fun i _ => period_summable (hs i) t)
  unfold integralReal
  rw [he]
  exact map_sum (meanCLM (G := PeriodGroup)) _ _

lemma weighted_bound (φ f : AF → ℝ) {B : ℝ}
    (hb : ∀ t, ‖φ t‖ ≤ B) (hf : ∀ t, 0 ≤ f t ∧ f t ≤ 1) :
    ∀ t, ‖φ t * f t‖ ≤ B := by
  intro t
  rw [norm_mul, Real.norm_of_nonneg (hf t).1]
  exact (mul_le_of_le_one_right (norm_nonneg _) (hf t).2).trans (hb t)

/-- Positivity of the literal invariant integral supplies a common small
parameter for finitely many nonnegative tests. This makes no ordinary
measurability assumption on any test. -/
theorem exists_small_nonnegative_tests {ι : Type*} (s : Finset ι)
    (φ : AF → ℝ) (f : ι → AF → ℝ) {N : ℕ} {B ε : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → φ t = 0)
    (hb : ∀ t, ‖φ t‖ ≤ B) (hp : ∀ t, 0 ≤ φ t)
    (hI : 0 < integralReal φ hs hb) (hε : 0 < ε)
    (hf : ∀ i t, 0 ≤ f i t ∧ f i t ≤ 1)
    (hz : ∀ i, integralReal (fun t => φ t * f i t)
      (fun t ht => by rw [hs t ht, zero_mul])
      (weighted_bound φ (f i) hb (hf i)) = 0) :
    ∃ t : AF, 0 < φ t ∧ ∀ i ∈ s, f i t < ε := by
  classical
  by_contra hn
  push Not at hn
  let g : AF → ℝ := fun t => ∑ i ∈ s, φ t * f i t
  have gs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → g t = 0 := by
    intro t ht
    simp [g, hs t ht]
  have gb : ∀ t, ‖g t‖ ≤ (s.card : ℝ) * B := by
    intro t
    calc
      _ ≤ ∑ i ∈ s, ‖φ t*f i t‖ := norm_sum_le _ _
      _ ≤ ∑ _i ∈ s, B := Finset.sum_le_sum (fun i _ => weighted_bound φ (f i) hb (hf i) t)
      _ = _ := by simp
  have gi : integralReal g gs gb = 0 := by
    rw [integralReal_sum s (fun i t => φ t*f i t)
      (fun i t ht => by rw [hs t ht, zero_mul])
      (fun i => weighted_bound φ (f i) hb (hf i)) gs gb]
    simp only [hz, Finset.sum_const_zero]
  have cs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → ε*φ t = 0 := by
    intro t ht; rw [hs t ht, mul_zero]
  have cb : ∀ t, ‖ε*φ t‖ ≤ |ε| * B := by
    intro t
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hb t) (abs_nonneg _)
  have hle : ∀ t, ε*φ t ≤ g t := by
    intro t
    by_cases ht : 0 < φ t
    · obtain ⟨i, hi, hfi⟩ := hn t ht
      have hterm : φ t*f i t ≤ g t :=
        Finset.single_le_sum (fun j _ => mul_nonneg (hp t) (hf j t).1) hi
      exact (by nlinarith : ε*φ t ≤ φ t*f i t).trans hterm
    · have hφ : φ t = 0 := le_antisymm (le_of_not_gt ht) (hp t)
      simp [g, hφ]
  have hmono := integralReal_mono (fun t => ε*φ t) g cs cb gs gb hle
  rw [integralReal_mul φ ε hs hb cs cb, gi] at hmono
  exact (not_le_of_gt (mul_pos hε hI)) hmono

end PlaneFiveColor.InvariantMean

namespace PlaneFiveColor.Spectral
open MeasureTheory Filter Topology
open scoped BigOperators
open InvariantMean

@[simp] lemma lineFourier_zero (ν : Measure D) [IsProbabilityMeasure ν] (a : E) :
    lineFourier ν a 0 = 1 := by
  simp [lineFourier]

lemma lineFourier_re_le_one (ν : Measure D) [IsProbabilityMeasure ν] (a : E) (t : F) :
    (lineFourier ν a t).re ≤ 1 :=
  (Complex.re_le_norm _).trans (lineFourier_norm_le ν a t)

/-- Real part of the checked vanishing line average, with the same invariant
integral and the same compact window. -/
lemma wild_line_average_re_zero (ν : Measure D) [IsProbabilityMeasure ν]
    (hν : IsWild ν) {a : E} (ha : a ≠ 0)
    (φ : ℝ → ℝ) (hc : UniformContinuous φ) {N : ℕ} {B : ℝ}
    (hs : ∀ t : ℝ, (N : ℝ) < |t| → φ t = 0)
    (hb : ∀ t, |φ t| ≤ B) :
    integralReal (fun t : F => φ t * (lineFourier ν a t).re)
      (fun t ht => by rw [hs t ht, zero_mul])
      (fun t => by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        exact (mul_le_of_le_one_right (abs_nonneg _)
          ((Complex.abs_re_le_norm _).trans (lineFourier_norm_le ν a t))).trans (hb t)) = 0 := by
  let f : F → ℂ := fun t => (φ t : ℂ) * lineFourier ν a t
  have fs : ∀ t : F, (N : ℝ) < |(t : ℝ)| → f t = 0 := by
    intro t ht; simp [f, hs t ht]
  have fb : ∀ t, ‖f t‖ ≤ B := by
    intro t
    dsimp [f]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_of_le_one_right (abs_nonneg _) (lineFourier_norm_le ν a t)).trans (hb t)
  have rs : ∀ t : F, (N : ℝ) < |(t : ℝ)| → (f t).re = 0 := by
    intro t ht; rw [fs t ht]; rfl
  have rb : ∀ t, ‖(f t).re‖ ≤ B := by
    intro t
    simpa only [Real.norm_eq_abs] using (Complex.abs_re_le_norm (f t)).trans (fb t)
  have hz : integralReal (fun t => (f t).re) rs rb = 0 := by
    rw [← integralComplex_re f fs fb rs rb]
    rw [show integralComplex f fs fb = 0 from wild_line_average_zero ν hν ha φ hc hs hb]
    rfl
  exact (integralReal_congr _ _ _ _ rs rb (fun t => by simp [f])).trans hz

/-- A compact tent window strictly inside the requested parameter radius. -/
lemma exists_positive_window {r : ℝ} (hr : 0 < r) :
    ∃ (φ : C(ℝ, ℝ)) (N : ℕ) (B : ℝ),
      (∀ t : ℝ, (N : ℝ) < |t| → φ t = 0) ∧
      (∀ t, ‖φ t‖ ≤ B) ∧ (∀ t, 0 ≤ φ t) ∧
      UniformContinuous φ ∧ (0 < ∫ t : ℝ, φ t) ∧
      (∀ t, 0 < φ t → |t| < r) := by
  let φ : C(ℝ, ℝ) := ⟨fun t => max 0 (r-|t|), by fun_prop⟩
  have hp (t : ℝ) : 0 ≤ φ t := le_max_left _ _
  have hb (t : ℝ) : ‖φ t‖ ≤ r := by
    rw [Real.norm_of_nonneg (hp t)]
    exact max_le hr.le (sub_le_self _ (abs_nonneg _))
  have houtside (t : ℝ) (ht : r ≤ |t|) : φ t = 0 := max_eq_left (sub_nonpos.mpr ht)
  have hcomp : HasCompactSupport φ := by
    apply HasCompactSupport.intro' (K := Set.Icc (-r) r) isCompact_Icc isClosed_Icc
    intro t ht
    apply houtside
    by_contra hn
    exact ht (abs_le.mp (le_of_lt (lt_of_not_ge hn)))
  have hi : 0 < ∫ t : ℝ, φ t :=
    φ.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hcomp hp
      (show φ 0 ≠ 0 by simpa [φ, max_eq_right hr.le] using hr.ne')
  obtain ⟨N, hN⟩ := exists_nat_gt r
  refine ⟨φ, N, r, (fun t ht => houtside t (le_of_lt (hN.trans ht))), hb, hp,
    hcomp.uniformContinuous_of_continuous φ.continuous, hi, ?_⟩
  intro t ht
  by_contra hn
  rw [houtside t (le_of_not_gt hn)] at ht
  exact lt_irrefl _ ht

theorem exists_small_wild_parameter {ι : Type*} (s : Finset ι) (hne : s.Nonempty)
    (ν : Measure D) [IsProbabilityMeasure ν] (hν : IsWild ν)
    (a : ι → E) (ha : ∀ i, a i ≠ 0)
    (hn : ∀ i t, 0 ≤ (lineFourier ν (a i) t).re)
    {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ t : F, t ≠ 0 ∧ |(t : ℝ)| < r ∧
      ∀ i ∈ s, (lineFourier ν (a i) t).re < ε := by
  obtain ⟨φ, N, B, hs, hb, hp, hc, hi, hradius⟩ := exists_positive_window hr
  have hz := fun i => wild_line_average_re_zero ν hν (ha i) φ hc hs
    (fun t => by simpa only [← Real.norm_eq_abs] using hb t)
  have hI : 0 < integralReal (fun t : F => φ t)
      (fun t ht => hs t ht) (fun t => hb t) := by
    rw [integralReal_ordinary φ hs hb]
    exact hi
  obtain ⟨t, ht, htest⟩ := exists_small_nonnegative_tests s
    (fun t : F => φ t) (fun i t => (lineFourier ν (a i) t).re)
    (fun t ht => hs t ht) (fun t => hb t) (fun t => hp t) hI hε
    (fun i t => ⟨hn i t, lineFourier_re_le_one ν (a i) t⟩)
    (fun i => by convert hz i using 1)
  refine ⟨t, ?_, hradius t ht, htest⟩
  intro he
  obtain ⟨i, his⟩ := hne
  have hh := htest i his
  rw [he, lineFourier_zero, Complex.one_re] at hh
  exact (not_lt_of_ge hε1) hh

end PlaneFiveColor.Spectral

open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
namespace EuclideanFiveColor.DifferenceFourier

variable {G Y : Type*} [MeasurableSpace G] [MeasurableSpace Y]
  [CommGroup G] [MeasurableMul₂ G] [MeasurableInv G]

noncomputable def differenceLaw (ν : Measure Y) (κ : Kernel Y G) [IsMarkovKernel κ] :
    Measure G := ((κ ×ₖ κ) ∘ₘ ν).map (fun p : G × G => p.1 / p.2)

instance differenceLaw_probability (ν : Measure Y) [IsProbabilityMeasure ν]
    (κ : Kernel Y G) [IsMarkovKernel κ] : IsProbabilityMeasure (differenceLaw ν κ) := by
  unfold differenceLaw
  infer_instance

variable (χ : G →* Circle)

omit [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G] in
lemma coe_character_div (d e : G) :
    (χ (d / e) : ℂ) = (χ d : ℂ) * conj (χ e : ℂ) := by
  rw [map_div, div_eq_mul_inv, Circle.coe_mul, Circle.coe_inv_eq_conj]

omit [MeasurableMul₂ G] [MeasurableInv G] in
lemma independent_coefficient (κ : Measure G) [IsProbabilityMeasure κ] :
    (∫ p : G × G, (χ (p.1 / p.2) : ℂ) ∂κ.prod κ) =
      (‖∫ d, (χ d : ℂ) ∂κ‖ ^ 2 : ℝ) := by
  calc
    _ = ∫ p : G × G, (χ p.1 : ℂ) * conj (χ p.2 : ℂ) ∂κ.prod κ :=
      integral_congr_ae (Filter.Eventually.of_forall (fun p => coe_character_div χ p.1 p.2))
    _ = (∫ d, (χ d : ℂ) ∂κ) * (∫ d, conj (χ d : ℂ) ∂κ) := by
      convert integral_prod_mul (fun d => (χ d : ℂ)) (fun d => conj (χ d : ℂ)) using 1 <;> infer_instance
    _ = _ := by rw [integral_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq]

lemma difference_coefficient (hχ : Measurable (fun d => (χ d : ℂ))) (ν : Measure Y) [IsProbabilityMeasure ν]
    (κ : Kernel Y G) [IsMarkovKernel κ] :
    (∫ d, (χ d : ℂ) ∂differenceLaw ν κ) =
      ((∫ y, (‖∫ d, (χ d : ℂ) ∂κ y‖ ^ 2 : ℝ) ∂ν : ℝ) : ℂ) := by
  have hm := hχ
  have hdiv : Measurable (fun p : G × G => p.1 / p.2) :=
    measurable_fst.div measurable_snd
  rw [differenceLaw, integral_map hdiv.aemeasurable hm.aestronglyMeasurable,
    Measure.comp_eq_comp_const_apply]
  rw [Kernel.integral_comp]
  · simp only [Kernel.const_apply, Kernel.prod_apply]
    change (∫ y, (∫ p : G × G, (χ (p.1 / p.2) : ℂ) ∂(κ y).prod (κ y)) ∂ν) = _
    rw [← integral_complex_ofReal]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun y => independent_coefficient χ (κ y))
  · exact Integrable.of_bound (hm.comp hdiv).aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun _ => (Circle.norm_coe _).le))

lemma difference_coefficient_nonneg (hχ : Measurable (fun d => (χ d : ℂ))) (ν : Measure Y) [IsProbabilityMeasure ν]
    (κ : Kernel Y G) [IsMarkovKernel κ] :
    0 ≤ (∫ d, (χ d : ℂ) ∂differenceLaw ν κ).re := by
  rw [difference_coefficient χ hχ]
  simp only [Complex.ofReal_re]
  apply integral_nonneg
  intro y
  positivity

end EuclideanFiveColor.DifferenceFourier

end
end
end
end

end OAI
