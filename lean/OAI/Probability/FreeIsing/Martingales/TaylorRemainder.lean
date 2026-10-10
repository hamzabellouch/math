import Mathlib

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology ENNReal

namespace Problem367.MartingaleTaylorRemainder

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem cubic_le_quadratic_add_quartic (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    |x| ^ 3 ≤ ε * x ^ 2 + (1 / (4 * ε)) * x ^ 4 := by
  have hpos : 0 < 4 * ε := mul_pos (by norm_num) hε
  have hid : (4 * ε) *
      (ε * x ^ 2 + (1 / (4 * ε)) * x ^ 4 - |x| ^ 3) =
      (x ^ 2 - 2 * ε * |x|) ^ 2 := by
    have hx2 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
    have hx4 : x ^ 4 = |x| ^ 4 := by nlinarith [sq_nonneg (x ^ 2 - |x| ^ 2)]
    rw [hx2, hx4]
    field_simp
    ring
  have hnon : 0 ≤ ε * x ^ 2 + (1 / (4 * ε)) * x ^ 4 - |x| ^ 3 := by
    apply (mul_nonneg_iff_of_pos_left hpos).1
    rw [hid]
    exact sq_nonneg _
  linarith

theorem integrable_abs_cube {D : Ω → ℝ}
    (hD : AEStronglyMeasurable D μ)
    (h2 : Integrable (fun ω => D ω ^ 2) μ)
    (h4 : Integrable (fun ω => D ω ^ 4) μ) :
    Integrable (fun ω => |D ω| ^ 3) μ := by
  apply (h2.add (h4.const_mul (1 / 4 : ℝ))).mono' (hD.norm.pow 3)
  filter_upwards [] with ω
  change abs (|D ω| ^ 3) ≤ D ω ^ 2 + (1 / 4 : ℝ) * D ω ^ 4
  simpa only [abs_of_nonneg (pow_nonneg (abs_nonneg (D ω)) 3),
    one_mul, mul_one] using cubic_le_quadratic_add_quartic (D ω) (by norm_num : (0 : ℝ) < 1)

theorem integral_sum_abs_cube_le {ι : Type*} (s : Finset ι) (D : ι → Ω → ℝ)
    (hD : ∀ i ∈ s, AEStronglyMeasurable (D i) μ)
    (h2 : ∀ i ∈ s, Integrable (fun ω => D i ω ^ 2) μ)
    (h4 : ∀ i ∈ s, Integrable (fun ω => D i ω ^ 4) μ)
    {ε : ℝ} (hε : 0 < ε) :
    (∫ ω, ∑ i ∈ s, |D i ω| ^ 3 ∂μ) ≤
      ε * (∫ ω, ∑ i ∈ s, D i ω ^ 2 ∂μ) +
        (1 / (4 * ε)) * (∫ ω, ∑ i ∈ s, D i ω ^ 4 ∂μ) := by
  have hc := integrable_finsetSum s (fun i hi => integrable_abs_cube (hD i hi) (h2 i hi) (h4 i hi))
  have hq := integrable_finsetSum s h2
  have hf := integrable_finsetSum s h4
  calc
    (∫ ω, ∑ i ∈ s, |D i ω| ^ 3 ∂μ) ≤
        ∫ ω, ε * (∑ i ∈ s, D i ω ^ 2) +
          (1 / (4 * ε)) * (∑ i ∈ s, D i ω ^ 4) ∂μ := by
      apply integral_mono hc ((hq.const_mul ε).add (hf.const_mul _))
      intro ω
      simpa only [Pi.add_apply, Finset.sum_add_distrib, Finset.mul_sum] using
        Finset.sum_le_sum (fun i (_ : i ∈ s) => cubic_le_quadratic_add_quartic (D i ω) hε)
    _ = _ := by rw [integral_add (hq.const_mul ε) (hf.const_mul _),
      integral_const_mul, integral_const_mul]

theorem tendsto_zero_of_young_bound {R C : ℕ → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hR : ∀ n, 0 ≤ R n)
    (hbound : ∀ ε : ℝ, 0 < ε → ∀ n, R n ≤ ε * B + C n / (4 * ε))
    (hC : Tendsto C atTop (𝓝 0)) : Tendsto R atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop] at hC ⊢
  intro ε hε
  let δ : ℝ := ε / (2 * (B + 1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  have ht : 0 < 2 * ε * δ := by positivity
  obtain ⟨N, hN⟩ := hC (2 * ε * δ) ht
  refine ⟨N, fun n hn => ?_⟩
  have hCn := hN n hn
  rw [Real.dist_eq, sub_zero] at hCn
  have hsmall : C n / (4 * δ) < ε / 2 := by
    apply (div_lt_iff₀ (by positivity : 0 < 4 * δ)).2
    have := lt_of_le_of_lt (le_abs_self (C n)) hCn
    nlinarith
  have hδB : δ * B < ε / 2 := by
    dsimp [δ]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by positivity : 0 < 2 * (B + 1))).2
    nlinarith
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hR n)]
  linarith [hbound δ hδ n]

theorem tendsto_integral_sum_abs_cube_zero {ι : Type*}
    (s : ℕ → Finset ι) (D : ℕ → ι → Ω → ℝ)
    (hD : ∀ n i, i ∈ s n → AEStronglyMeasurable (D n i) μ)
    (h2 : ∀ n i, i ∈ s n → Integrable (fun ω => D n i ω ^ 2) μ)
    (h4 : ∀ n i, i ∈ s n → Integrable (fun ω => D n i ω ^ 4) μ)
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ n, (∫ ω, ∑ i ∈ s n, D n i ω ^ 2 ∂μ) ≤ B)
    (hfourth : Tendsto (fun n => ∫ ω, ∑ i ∈ s n, D n i ω ^ 4 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, ∑ i ∈ s n, |D n i ω| ^ 3 ∂μ) atTop (𝓝 0) := by
  apply tendsto_zero_of_young_bound
    (C := fun n => ∫ ω, ∑ i ∈ s n, D n i ω ^ 4 ∂μ) hB
  · intro n
    exact integral_nonneg (fun ω => Finset.sum_nonneg (fun i _ => pow_nonneg (abs_nonneg _) _))
  · intro ε hε n
    have h := integral_sum_abs_cube_le (s n) (D n) (hD n) (h2 n) (h4 n) hε
    have hb := mul_le_mul_of_nonneg_left (hbound n) hε.le
    calc
      _ ≤ ε * (∫ ω, ∑ i ∈ s n, D n i ω ^ 2 ∂μ) +
          (1 / (4 * ε)) * (∫ ω, ∑ i ∈ s n, D n i ω ^ 4 ∂μ) := h
      _ ≤ ε * B + (1 / (4 * ε)) * (∫ ω, ∑ i ∈ s n, D n i ω ^ 4 ∂μ) :=
        add_le_add hb le_rfl
      _ = _ := by ring
  · exact hfourth

theorem remainder_L1_of_cubic_bound {ι : Type*}
    (s : ℕ → Finset ι) (D : ℕ → ι → Ω → ℝ) (R : ℕ → Ω → ℝ)
    (hD : ∀ n i, i ∈ s n → AEStronglyMeasurable (D n i) μ)
    (h2 : ∀ n i, i ∈ s n → Integrable (fun ω => D n i ω ^ 2) μ)
    (h4 : ∀ n i, i ∈ s n → Integrable (fun ω => D n i ω ^ 4) μ)
    (hR : ∀ n, AEStronglyMeasurable (R n) μ)
    {B C : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ n, (∫ ω, ∑ i ∈ s n, D n i ω ^ 2 ∂μ) ≤ B)
    (hfourth : Tendsto (fun n => ∫ ω, ∑ i ∈ s n, D n i ω ^ 4 ∂μ) atTop (𝓝 0))
    (hrem : ∀ n, ∀ᵐ ω ∂μ, |R n ω| ≤ C * ∑ i ∈ s n, |D n i ω| ^ 3) :
    (∀ n, Integrable (R n) μ) ∧
      Tendsto (fun n => ∫ ω, |R n ω| ∂μ) atTop (𝓝 0) := by
  have hc (n : ℕ) : Integrable (fun ω => ∑ i ∈ s n, |D n i ω| ^ 3) μ :=
    integrable_finsetSum (s n) (fun i hi => integrable_abs_cube (hD n i hi) (h2 n i hi) (h4 n i hi))
  have hr (n : ℕ) : Integrable (R n) μ := by
    apply ((hc n).const_mul C).mono' (hR n)
    simpa only [Real.norm_eq_abs] using hrem n
  refine ⟨hr, ?_⟩
  have hlim : Tendsto (fun n => C * (∫ ω, ∑ i ∈ s n, |D n i ω| ^ 3 ∂μ)) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_integral_sum_abs_cube_zero s D hD h2 h4 hB hbound hfourth).const_mul C
  refine squeeze_zero (fun n => integral_nonneg (fun _ => abs_nonneg _)) (fun n => ?_) hlim
  calc
    _ ≤ ∫ ω, C * ∑ i ∈ s n, |D n i ω| ^ 3 ∂μ :=
      integral_mono_ae (hr n).abs ((hc n).const_mul C) (hrem n)
    _ = _ := integral_const_mul _ _

theorem ae_eq_add_of_taylor_L1_limits
    {Y L Q : Ω → ℝ} {Ln Qn : ℕ → Ω → ℝ}
    (hY : Integrable Y μ) (hL : Integrable L μ) (hQ : Integrable Q μ)
    (hLn : ∀ n, Integrable (Ln n) μ) (hQn : ∀ n, Integrable (Qn n) μ)
    (hrem : Tendsto (fun n => ∫ ω, |Y ω - Ln n ω - Qn n ω| ∂μ) atTop (𝓝 0))
    (hlin : Tendsto (fun n => ∫ ω, |Ln n ω - L ω| ∂μ) atTop (𝓝 0))
    (hquad : Tendsto (fun n => ∫ ω, |Qn n ω - Q ω| ∂μ) atTop (𝓝 0)) :
    Y =ᵐ[μ] fun ω => L ω + Q ω := by
  have hineq (n : ℕ) :
      (∫ ω, |Y ω - L ω - Q ω| ∂μ) ≤
        (∫ ω, |Y ω - Ln n ω - Qn n ω| ∂μ) +
        (∫ ω, |Ln n ω - L ω| ∂μ) + (∫ ω, |Qn n ω - Q ω| ∂μ) := by
    calc
      _ ≤ ∫ ω, |Y ω - Ln n ω - Qn n ω| +
          |Ln n ω - L ω| + |Qn n ω - Q ω| ∂μ := by
        apply integral_mono ((hY.sub hL).sub hQ).abs
          ((((hY.sub (hLn n)).sub (hQn n)).abs.add ((hLn n).sub hL).abs).add
            ((hQn n).sub hQ).abs)
        intro ω
        have he : Y ω - L ω - Q ω =
            (Y ω - Ln n ω - Qn n ω) + (Ln n ω - L ω) + (Qn n ω - Q ω) := by ring
        simp only [Pi.sub_apply, Pi.add_apply]
        rw [he]
        exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ = _ := by
        have h1 : Integrable (fun ω => |Y ω - Ln n ω - Qn n ω|) μ :=
          ((hY.sub (hLn n)).sub (hQn n)).abs
        have h2 : Integrable (fun ω => |Ln n ω - L ω|) μ := ((hLn n).sub hL).abs
        have h3 : Integrable (fun ω => |Qn n ω - Q ω|) μ := ((hQn n).sub hQ).abs
        have h12 : Integrable (fun ω => |Y ω - Ln n ω - Qn n ω| + |Ln n ω - L ω|) μ := h1.add h2
        rw [integral_add h12 h3, integral_add h1 h2]

  have hz : (∫ ω, |Y ω - L ω - Q ω| ∂μ) = 0 := by
    apply le_antisymm
    · have hlim := (hrem.add hlin).add hquad
      simpa only [zero_add] using ge_of_tendsto hlim (Eventually.of_forall hineq)
    · exact integral_nonneg (fun _ => abs_nonneg _)
  have hae := (integral_eq_zero_iff_of_nonneg (fun ω => abs_nonneg (Y ω - L ω - Q ω))
    ((hY.sub hL).sub hQ).abs).1 hz
  filter_upwards [hae] with ω hω
  have hh := abs_eq_zero.mp hω
  linarith

end Problem367.MartingaleTaylorRemainder

end

end OAI
