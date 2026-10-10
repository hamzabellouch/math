import OAI.NumberTheory.JointDickman.Amplification.PublishedInputs
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

namespace OAI

/-!
# Finite interpolation and the published real short-interval input

The multiplicative interpolants used for a centered label have separate
short-average errors. Cauchy–Schwarz combines these errors;
the input is explicitly the published `RealShortIntervalInput`.
-/

namespace JointDickman.PublishedInputs

open Filter MeasureTheory
open scoped Topology

theorem measurable_realShortAverage (f : ArithmeticFunction ℝ) (H : ℝ) :
    Measurable (realShortAverage f H) := by
  have hm : Measurable (fun p : ℕ × ℕ => ∑ n ∈ Finset.Ioc p.1 p.2, f n) :=
    measurable_of_countable _
  exact (hm.comp (Nat.measurable_floor.prodMk
    (measurable_id.add_const H).nat_floor)).div_const H

theorem abs_realShortAverage_le (f : ArithmeticFunction ℝ)
    (hf : ∀ n : ℕ, |f n| ≤ 1) {H z b : ℝ} (hH : 0 < H) (hz : z ≤ b) :
    |realShortAverage f H z| ≤ (⌊b + H⌋₊ : ℝ) / H := by
  rw [realShortAverage, abs_div, abs_of_pos hH]
  apply div_le_div_of_nonneg_right _ hH.le
  calc
    |∑ n ∈ Finset.Ioc ⌊z⌋₊ ⌊z + H⌋₊, f n| ≤
        ∑ n ∈ Finset.Ioc ⌊z⌋₊ ⌊z + H⌋₊, |f n| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ Finset.Ioc ⌊z⌋₊ ⌊z + H⌋₊, (1 : ℝ) :=
      Finset.sum_le_sum fun n _ => hf n
    _ = ((Finset.Ioc ⌊z⌋₊ ⌊z + H⌋₊).card : ℝ) := by simp
    _ ≤ (⌊b + H⌋₊ : ℝ) := by
      exact_mod_cast (show (Finset.Ioc ⌊z⌋₊ ⌊z + H⌋₊).card ≤ ⌊b + H⌋₊ from by
        simpa only [Nat.card_Ioc] using (Nat.sub_le ⌊z + H⌋₊ ⌊z⌋₊).trans
          (Nat.floor_mono (by linarith : z + H ≤ b + H)))

theorem realShortAverage_sub_sq_integrable (f : ArithmeticFunction ℝ)
    (hf : ∀ n : ℕ, |f n| ≤ 1) {H : ℝ} (hH : 0 < H) (c a b : ℝ) :
    IntervalIntegrable (fun z => (realShortAverage f H z - c) ^ 2) volume a b := by
  let K : ℝ := (⌊max a b + H⌋₊ : ℝ) / H + |c|
  have hm := ((measurable_realShortAverage f H).sub_const c).pow_const 2
  refine (intervalIntegrable_const (c := K ^ 2)).mono_fun' hm.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with z hz
  have hz' : z ≤ max a b := hz.2
  have hbound : |realShortAverage f H z - c| ≤ K :=
    (abs_sub _ _).trans (add_le_add (abs_realShortAverage_le f hf hH hz') le_rfl)
  simpa only [Real.norm_eq_abs, abs_pow, sq_abs] using
    pow_le_pow_left₀ (abs_nonneg _) hbound 2

/-- The centered linear combination appearing after interpolation. -/
noncomputable def centeredCombination {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (f : ι → ArithmeticFunction ℝ) (H X z : ℝ) : ℝ :=
  ∑ i ∈ s, c i * (realShortAverage (f i) H z - realLongAverage (f i) X)

/-- The uncentered interpolated short average. -/
noncomputable def shortCombination {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (f : ι → ArithmeticFunction ℝ) (H z : ℝ) : ℝ :=
  ∑ i ∈ s, c i * realShortAverage (f i) H z

/-- Its combined long mean. Individual means need not vanish. -/
noncomputable def longCombination {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (f : ι → ArithmeticFunction ℝ) (X : ℝ) : ℝ :=
  ∑ i ∈ s, c i * realLongAverage (f i) X

theorem shortCombination_eq_centered_add_long {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (f : ι → ArithmeticFunction ℝ) (H X z : ℝ) :
    shortCombination s c f H z =
      centeredCombination s c f H X z + longCombination s c f X := by
  simp only [shortCombination, centeredCombination, longCombination, mul_sub,
    Finset.sum_sub_distrib]
  ring

theorem centeredCombination_sq_le {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (f : ι → ArithmeticFunction ℝ) (H X z : ℝ) :
    (centeredCombination s c f H X z) ^ 2 ≤
      (∑ i ∈ s, c i ^ 2) *
        ∑ i ∈ s, (realShortAverage (f i) H z - realLongAverage (f i) X) ^ 2 :=
  Finset.sum_mul_sq_le_sq_mul_sq s c
    (fun i => realShortAverage (f i) H z - realLongAverage (f i) X)

theorem measurable_centeredCombination {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (f : ι → ArithmeticFunction ℝ) (H X : ℝ) :
    Measurable (centeredCombination s c f H X) := by
  exact Finset.measurable_sum _ fun i _ =>
    ((measurable_realShortAverage (f i) H).sub_const _).const_mul _

theorem centeredCombination_sq_integrable {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (f : ι → ArithmeticFunction ℝ)
    (hf : ∀ i ∈ s, ∀ n : ℕ, |f i n| ≤ 1) {H : ℝ} (hH : 0 < H) (X : ℝ) :
    IntervalIntegrable (fun z => (centeredCombination s c f H X z) ^ 2)
      volume X (2 * X) := by
  have hsum : IntervalIntegrable
      (fun z => (∑ i ∈ s, c i ^ 2) *
        ∑ i ∈ s, (realShortAverage (f i) H z - realLongAverage (f i) X) ^ 2)
      volume X (2 * X) := by
    apply IntervalIntegrable.const_mul
    convert IntervalIntegrable.sum s (fun i hi =>
      realShortAverage_sub_sq_integrable (f i) (hf i hi) hH
        (realLongAverage (f i) X) X (2 * X)) using 1
    ext z
    simp only [Finset.sum_apply]
  apply hsum.mono_fun'
    (((measurable_centeredCombination s c f H X).pow_const 2).aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun z => by
    simpa only [Real.norm_eq_abs, abs_pow, sq_abs] using
      centeredCombination_sq_le s c f H X z

/-- Finite linear interpolation preserves the uniform mean-square estimate.
The same witness `r` works for every fixed finite family. -/
theorem real_input_finite_combination_bound (hMR : RealShortIntervalInput) :
    ∃ r : ℝ → ℝ, Tendsto r atTop (𝓝 0) ∧
      ∀ {ι : Type*} (s : Finset ι) (c : ι → ℝ) (f : ι → ArithmeticFunction ℝ),
      (∀ i ∈ s, (f i).IsMultiplicative) →
      (∀ i ∈ s, ∀ n : ℕ, |f i n| ≤ 1) →
      ∀ H X : ℝ, 2 ≤ H → H ≤ X →
        (1 / X) * (∫ z in X..2 * X, (centeredCombination s c f H X z) ^ 2) ≤
          (∑ i ∈ s, c i ^ 2) * (s.card : ℝ) * r H := by
  obtain ⟨r, hr, hbound⟩ := hMR
  refine ⟨r, hr, ?_⟩
  intro ι s c f hmult hf H X hH hHX
  have hHpos : 0 < H := by linarith
  have hXpos : 0 < X := lt_of_lt_of_le hHpos hHX
  have hK : 0 ≤ ∑ i ∈ s, c i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hfi (i : ι) (hi : i ∈ s) : IntervalIntegrable
      (fun z => (realShortAverage (f i) H z - realLongAverage (f i) X) ^ 2)
      volume X (2 * X) := realShortAverage_sub_sq_integrable (f i) (hf i hi) hHpos _ _ _
  have hsum : IntervalIntegrable
      (fun z => (∑ i ∈ s, c i ^ 2) *
        ∑ i ∈ s, (realShortAverage (f i) H z - realLongAverage (f i) X) ^ 2)
      volume X (2 * X) := by
    simpa only [Finset.sum_apply] using
      (IntervalIntegrable.sum s hfi).const_mul (∑ i ∈ s, c i ^ 2)
  have hint := intervalIntegral.integral_mono (by linarith : X ≤ 2 * X)
    (centeredCombination_sq_integrable s c f hf hHpos X) hsum
    (centeredCombination_sq_le s c f H X)
  calc
    _ ≤ (1 / X) * ((∑ i ∈ s, c i ^ 2) *
        ∫ z in X..2 * X,
          ∑ i ∈ s, (realShortAverage (f i) H z - realLongAverage (f i) X) ^ 2) := by
      simpa only [intervalIntegral.integral_const_mul] using
        mul_le_mul_of_nonneg_left hint (by positivity : 0 ≤ 1 / X)
    _ = (∑ i ∈ s, c i ^ 2) *
        ∑ i ∈ s, (1 / X) *
          (∫ z in X..2 * X,
            (realShortAverage (f i) H z - realLongAverage (f i) X) ^ 2) := by
      rw [intervalIntegral.integral_finsetSum hfi, ← Finset.mul_sum]
      ring
    _ ≤ (∑ i ∈ s, c i ^ 2) * ∑ _i ∈ s, r H := by
      apply mul_le_mul_of_nonneg_left _ hK
      apply Finset.sum_le_sum
      intro i hi
      simpa only [sq_abs] using hbound (f i) (hmult i hi) (hf i hi) H X hH hHX
    _ = _ := by simp [mul_assoc]

/-- A fixed finite number of multiplicative interpolants has vanishing combined
centered short-average energy as the length tends to infinity. The functions
themselves may vary with the scale, as the paper's bin interpolants do. -/
theorem centeredCombination_tendsto_zero (hMR : RealShortIntervalInput)
    {ι : Type*} (s : Finset ι) (c : ι → ℝ) (f : ℕ → ι → ArithmeticFunction ℝ)
    (hmult : ∀ k, ∀ i ∈ s, (f k i).IsMultiplicative)
    (hf : ∀ k, ∀ i ∈ s, ∀ n : ℕ, |f k i n| ≤ 1)
    (H X : ℕ → ℝ) (hH : Tendsto H atTop atTop)
    (hHX : ∀ᶠ n in atTop, H n ≤ X n) :
    Tendsto (fun n => (1 / X n) *
      (∫ z in X n..2 * X n, (centeredCombination s c (f n) (H n) (X n) z) ^ 2))
      atTop (𝓝 0) := by
  obtain ⟨r, hr, hbound⟩ := real_input_finite_combination_bound hMR
  have hlarge : ∀ᶠ n in atTop, 2 ≤ H n := hH.eventually (eventually_ge_atTop 2)
  have hlower : ∀ᶠ n in atTop, 0 ≤ (1 / X n) *
      (∫ z in X n..2 * X n, (centeredCombination s c (f n) (H n) (X n) z) ^ 2) := by
    filter_upwards [hlarge, hHX] with n hn hnX
    have hX : 0 < X n := by linarith
    apply mul_nonneg (by positivity)
    exact intervalIntegral.integral_nonneg (by linarith) fun _ _ => sq_nonneg _
  have hupper := hlarge.and hHX |>.mono fun n hn =>
    hbound s c (f n) (hmult n) (hf n) (H n) (X n) hn.1 hn.2
  apply squeeze_zero' hlower hupper
  simpa using (tendsto_const_nhds.mul (hr.comp hH) :
    Tendsto (fun n => ((∑ i ∈ s, c i ^ 2) * (s.card : ℝ)) * r (H n)) atTop
      (𝓝 (((∑ i ∈ s, c i ^ 2) * (s.card : ℝ)) * 0)))

theorem meanSquare_add_const_le {u : ℝ → ℝ} (hu : Measurable u)
    {X : ℝ} (hX : 0 < X)
    (huint : IntervalIntegrable (fun z => u z ^ 2) volume X (2 * X)) (a : ℝ) :
    (1 / X) * (∫ z in X..2 * X, (u z + a) ^ 2) ≤
      2 * ((1 / X) * (∫ z in X..2 * X, u z ^ 2)) + 2 * a ^ 2 := by
  have hpoint (z : ℝ) : (u z + a) ^ 2 ≤ 2 * u z ^ 2 + 2 * a ^ 2 := by
    nlinarith [sq_nonneg (u z - a)]
  have hrhs : IntervalIntegrable (fun z => 2 * u z ^ 2 + 2 * a ^ 2)
      volume X (2 * X) := (huint.const_mul 2).add intervalIntegrable_const
  have hlhs : IntervalIntegrable (fun z => (u z + a) ^ 2)
      volume X (2 * X) := hrhs.mono_fun' (((hu.add_const a).pow_const 2).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun z => by
          simpa only [Real.norm_eq_abs, abs_pow, sq_abs] using hpoint z)
  have hmono := intervalIntegral.integral_mono (by linarith : X ≤ 2 * X)
    hlhs hrhs hpoint
  have h := mul_le_mul_of_nonneg_left hmono (by positivity : 0 ≤ 1 / X)
  rw [intervalIntegral.integral_add (huint.const_mul 2) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at h
  convert h using 1
  field_simp
  ring

/-- The application needed after interpolating a centered label: only the
combined long mean must vanish; its individual multiplicative summands may
have nonzero long means. -/
theorem shortCombination_tendsto_zero (hMR : RealShortIntervalInput)
    {ι : Type*} (s : Finset ι) (c : ι → ℝ) (f : ℕ → ι → ArithmeticFunction ℝ)
    (hmult : ∀ k, ∀ i ∈ s, (f k i).IsMultiplicative)
    (hf : ∀ k, ∀ i ∈ s, ∀ n : ℕ, |f k i n| ≤ 1)
    (H X : ℕ → ℝ) (hH : Tendsto H atTop atTop)
    (hHX : ∀ᶠ n in atTop, H n ≤ X n)
    (hlong : Tendsto (fun n => longCombination s c (f n) (X n)) atTop (𝓝 0)) :
    Tendsto (fun n => (1 / X n) *
      (∫ z in X n..2 * X n, (shortCombination s c (f n) (H n) z) ^ 2))
      atTop (𝓝 0) := by
  have hcenter := centeredCombination_tendsto_zero hMR s c f hmult hf H X hH hHX
  have hlarge : ∀ᶠ n in atTop, 2 ≤ H n := hH.eventually (eventually_ge_atTop 2)
  have hlower : ∀ᶠ n in atTop, 0 ≤ (1 / X n) *
      (∫ z in X n..2 * X n, (shortCombination s c (f n) (H n) z) ^ 2) := by
    filter_upwards [hlarge, hHX] with n hn hnX
    have hX : 0 < X n := by linarith
    exact mul_nonneg (by positivity)
      (intervalIntegral.integral_nonneg (by linarith) fun _ _ => sq_nonneg _)
  have hupper : ∀ᶠ n in atTop,
      (1 / X n) * (∫ z in X n..2 * X n, (shortCombination s c (f n) (H n) z) ^ 2) ≤
        2 * ((1 / X n) *
          (∫ z in X n..2 * X n, (centeredCombination s c (f n) (H n) (X n) z) ^ 2)) +
          2 * longCombination s c (f n) (X n) ^ 2 := by
    filter_upwards [hlarge, hHX] with n hn hnX
    have hX : 0 < X n := by linarith
    simpa only [← shortCombination_eq_centered_add_long] using
      meanSquare_add_const_le (measurable_centeredCombination s c (f n) (H n) (X n)) hX
        (centeredCombination_sq_integrable s c (f n) (hf n) (by linarith) (X n))
        (longCombination s c (f n) (X n))
  apply squeeze_zero' hlower hupper
  simpa using (hcenter.const_mul 2).add ((hlong.pow 2).const_mul 2)


/-- The iterated-limit form used when the short length is fixed in the inner
scale limit. This is the principal-character part of `labels-short`. -/
theorem shortCombination_eventually_eventually (hMR : RealShortIntervalInput)
    {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (f : ℕ → ℕ → ι → ArithmeticFunction ℝ)
    (hmult : ∀ B n, ∀ i ∈ s, (f B n i).IsMultiplicative)
    (hf : ∀ B n, ∀ i ∈ s, ∀ k : ℕ, |f B n i k| ≤ 1)
    (H : ℕ → ℝ) (X : ℕ → ℕ → ℝ) (hH : Tendsto H atTop atTop)
    (hHX : ∀ B, ∀ᶠ n in atTop, H B ≤ X B n)
    (hlong : ∀ B, Tendsto (fun n => longCombination s c (f B n) (X B n))
      atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ B in atTop, ∀ᶠ n in atTop,
      (1 / X B n) * (∫ z in X B n..2 * X B n,
        (shortCombination s c (f B n) (H B) z) ^ 2) < ε := by
  obtain ⟨r, hr, hbound⟩ := real_input_finite_combination_bound hMR
  intro ε hε
  have hlarge : ∀ᶠ B in atTop, 2 ≤ H B := hH.eventually (eventually_ge_atTop 2)
  have hrsmall : ∀ᶠ B in atTop,
      2 * ((∑ i ∈ s, c i ^ 2) * (s.card : ℝ) * r (H B)) < ε / 2 := by
    have ht := ((hr.comp hH).const_mul ((∑ i ∈ s, c i ^ 2) * (s.card : ℝ))).const_mul 2
    exact ht.eventually (gt_mem_nhds (by simpa using half_pos hε))
  filter_upwards [hlarge, hrsmall] with B hB hBr
  have hlongsmall : ∀ᶠ n in atTop,
      2 * longCombination s c (f B n) (X B n) ^ 2 < ε / 2 := by
    have ht := ((hlong B).pow 2).const_mul 2
    exact ht.eventually (gt_mem_nhds (by simpa using half_pos hε))
  filter_upwards [hHX B, hlongsmall] with n hn hnlong
  have hX : 0 < X B n := by linarith
  have hmean := meanSquare_add_const_le
    (measurable_centeredCombination s c (f B n) (H B) (X B n)) hX
    (centeredCombination_sq_integrable s c (f B n) (hf B n) (by linarith) (X B n))
    (longCombination s c (f B n) (X B n))
  have hb := hbound s c (f B n) (hmult B n) (hf B n) (H B) (X B n) hB hn
  simp only [← shortCombination_eq_centered_add_long] at hmean
  linarith

theorem shortCombination_sq_integrable {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (f : ι → ArithmeticFunction ℝ)
    (hf : ∀ i ∈ s, ∀ n : ℕ, |f i n| ≤ 1) {H : ℝ} (hH : 0 < H) (X : ℝ) :
    IntervalIntegrable (fun z => shortCombination s c f H z ^ 2)
      volume X (2 * X) := by
  have hc := centeredCombination_sq_integrable s c f hf hH X
  have hrhs : IntervalIntegrable
      (fun z => 2 * centeredCombination s c f H X z ^ 2 +
        2 * longCombination s c f X ^ 2) volume X (2 * X) :=
    (hc.const_mul 2).add intervalIntegrable_const
  have hm : Measurable (shortCombination s c f H) :=
    Finset.measurable_sum _ fun i _ =>
      (measurable_realShortAverage (f i) H).const_mul _
  apply hrhs.mono_fun' (hm.pow_const 2).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  simp only [Real.norm_eq_abs, abs_pow, sq_abs]
  rw [shortCombination_eq_centered_add_long s c f H X z]
  nlinarith [sq_nonneg (centeredCombination s c f H X z - longCombination s c f X)]

/-- The coefficients in the manuscript's real multiplicative interpolation
are complex, even for the principal-character term. -/
noncomputable def complexShortCombination {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) (f : ι → ArithmeticFunction ℝ) (H z : ℝ) : ℂ :=
  ∑ i ∈ s, c i * (realShortAverage (f i) H z : ℂ)

noncomputable def complexLongCombination {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) (f : ι → ArithmeticFunction ℝ) (X : ℝ) : ℂ :=
  ∑ i ∈ s, c i * (realLongAverage (f i) X : ℂ)

theorem complexShortCombination_norm_sq {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) (f : ι → ArithmeticFunction ℝ) (H z : ℝ) :
    ‖complexShortCombination s c f H z‖ ^ 2 =
      shortCombination s (fun i => (c i).re) f H z ^ 2 +
        shortCombination s (fun i => (c i).im) f H z ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq]
  simp [complexShortCombination, shortCombination, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im, pow_two]

theorem complexShortCombination_energy {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) (f : ι → ArithmeticFunction ℝ)
    (hf : ∀ i ∈ s, ∀ n : ℕ, |f i n| ≤ 1) {H : ℝ} (hH : 0 < H) (X : ℝ) :
    (1 / X) * (∫ z in X..2 * X, ‖complexShortCombination s c f H z‖ ^ 2) =
      (1 / X) * (∫ z in X..2 * X,
        shortCombination s (fun i => (c i).re) f H z ^ 2) +
      (1 / X) * (∫ z in X..2 * X,
        shortCombination s (fun i => (c i).im) f H z ^ 2) := by
  simp_rw [complexShortCombination_norm_sq]
  rw [intervalIntegral.integral_add
    (shortCombination_sq_integrable s _ f hf hH X)
    (shortCombination_sq_integrable s _ f hf hH X), mul_add]

/-- Complex coefficients require no complex multiplicative input for the
principal-character part: apply the real input to both coefficient parts. -/
theorem complexShortCombination_eventually_eventually (hMR : RealShortIntervalInput)
    {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (f : ℕ → ℕ → ι → ArithmeticFunction ℝ)
    (hmult : ∀ B n, ∀ i ∈ s, (f B n i).IsMultiplicative)
    (hf : ∀ B n, ∀ i ∈ s, ∀ k : ℕ, |f B n i k| ≤ 1)
    (H : ℕ → ℝ) (X : ℕ → ℕ → ℝ) (hH : Tendsto H atTop atTop)
    (hHX : ∀ B, ∀ᶠ n in atTop, H B ≤ X B n)
    (hlong : ∀ B, Tendsto (fun n => complexLongCombination s c (f B n) (X B n))
      atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ B in atTop, ∀ᶠ n in atTop,
      (1 / X B n) * (∫ z in X B n..2 * X B n,
        ‖complexShortCombination s c (f B n) (H B) z‖ ^ 2) < ε := by
  have hlongre (B : ℕ) :
      Tendsto (fun n => longCombination s (fun i => (c i).re) (f B n) (X B n))
        atTop (𝓝 0) := by
    simpa [Function.comp_def, complexLongCombination, longCombination, Complex.mul_re] using (Complex.continuous_re.tendsto (0 : ℂ)).comp (hlong B)
  have hlongim (B : ℕ) :
      Tendsto (fun n => longCombination s (fun i => (c i).im) (f B n) (X B n))
        atTop (𝓝 0) := by
    simpa [Function.comp_def, complexLongCombination, longCombination, Complex.mul_im] using (Complex.continuous_im.tendsto (0 : ℂ)).comp (hlong B)
  intro ε hε
  have hre := shortCombination_eventually_eventually hMR s (fun i => (c i).re)
    f hmult hf H X hH hHX hlongre (ε / 2) (half_pos hε)
  have him := shortCombination_eventually_eventually hMR s (fun i => (c i).im)
    f hmult hf H X hH hHX hlongim (ε / 2) (half_pos hε)
  have hlarge : ∀ᶠ B in atTop, 2 ≤ H B := hH.eventually (eventually_ge_atTop 2)
  filter_upwards [hre, him, hlarge] with B hBre hBim hB
  filter_upwards [hBre, hBim] with n hnre hnim
  rw [complexShortCombination_energy s c (f B n) (hf B n) (by linarith)]
  linarith

end JointDickman.PublishedInputs

end OAI
