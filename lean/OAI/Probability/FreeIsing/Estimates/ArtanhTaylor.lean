import OAI.Probability.FreeIsing.Estimates.MessageFunction

namespace OAI

noncomputable section

open Set Filter
open scoped Topology BigOperators

namespace Problem367.ArtanhTaylor

lemma denominator_pos {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    0 < 1 - x ^ 2 := by
  nlinarith [hx.1, hx.2]

theorem contDiffAt_artanh {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1)
    (n : WithTop ENat) : ContDiffAt ℝ n Real.artanh x := by
  have hm : 0 < 1 - x := by linarith [hx.2]
  have hp : 0 < 1 + x := by linarith [hx.1]
  have hq : 0 < (1 + x) / (1 - x) := div_pos hp hm
  unfold Real.artanh
  exact (((contDiffAt_const.add contDiffAt_id).div
    (contDiffAt_const.sub contDiffAt_id) hm.ne').sqrt hq.ne').log
      (Real.sqrt_pos.mpr hq).ne'

lemma hasDerivAt_first {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun y : ℝ => 1 / (1 - y ^ 2))
      (2 * x / (1 - x ^ 2) ^ 2) x := by
  have h := (hasDerivAt_const x (1 : ℝ)).div
    (((hasDerivAt_id x).pow 2).const_sub 1) (denominator_pos hx).ne'
  apply h.congr_deriv
  dsimp
  ring

lemma hasDerivAt_second {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun y : ℝ => 2 * y / (1 - y ^ 2) ^ 2)
      ((2 + 6 * x ^ 2) / (1 - x ^ 2) ^ 3) x := by
  have h := ((hasDerivAt_id x).const_mul 2).div
    ((((hasDerivAt_id x).pow 2).const_sub 1).pow 2)
    (pow_ne_zero 2 (denominator_pos hx).ne')
  apply h.congr_deriv
  dsimp
  field_simp [(denominator_pos hx).ne']
  ring

lemma iteratedDeriv_two {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    iteratedDeriv 2 Real.artanh x = 2 * x / (1 - x ^ 2) ^ 2 := by
  have he : deriv Real.artanh =ᶠ[𝓝 x] (fun y : ℝ => 1 / (1 - y ^ 2)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact (hasDerivAt_artanh_interval hy).deriv
  rw [show 2 = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  exact he.deriv_eq.trans (hasDerivAt_first hx).deriv

lemma iteratedDeriv_three {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    iteratedDeriv 3 Real.artanh x = (2 + 6 * x ^ 2) / (1 - x ^ 2) ^ 3 := by
  have he : iteratedDeriv 2 Real.artanh =ᶠ[𝓝 x]
      (fun y : ℝ => 2 * y / (1 - y ^ 2) ^ 2) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact iteratedDeriv_two hy
  rw [show 3 = 2 + 1 from rfl, iteratedDeriv_succ]
  exact he.deriv_eq.trans (hasDerivAt_second hx).deriv

theorem abs_iteratedDeriv_three_le {r x : ℝ} (hr : r < 1)
    (hx : |x| ≤ r) :
    |iteratedDeriv 3 Real.artanh x| ≤ 8 / (1 - r ^ 2) ^ 3 := by
  have hr0 : 0 ≤ r := (abs_nonneg x).trans hx
  have hx1 : |x| < 1 := hx.trans_lt hr
  have hmem : x ∈ Ioo (-1 : ℝ) 1 := abs_lt.mp hx1
  have hsq : x ^ 2 ≤ r ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg x) hr0).2 hx
  have hrden : 0 < 1 - r ^ 2 := by nlinarith
  have hxden := denominator_pos hmem
  rw [iteratedDeriv_three hmem, abs_of_nonneg (by positivity)]
  calc
    (2 + 6 * x ^ 2) / (1 - x ^ 2) ^ 3 ≤ 8 / (1 - x ^ 2) ^ 3 := by
      gcongr
      nlinarith
    _ ≤ 8 / (1 - r ^ 2) ^ 3 := by
      gcongr

theorem abs_remainder_le {r x y : ℝ} (hr : r < 1)
    (hx : |x| ≤ r) (hy : |y| ≤ r) :
    |Real.artanh y - Real.artanh x - (y - x) / (1 - x ^ 2) -
      x * (y - x) ^ 2 / (1 - x ^ 2) ^ 2| ≤
        (8 / (1 - r ^ 2) ^ 3) * |y - x| ^ 3 := by
  by_cases hxy : x = y
  · subst y
    simp
  have hr0 : 0 ≤ r := (abs_nonneg x).trans hx
  have hrden : 0 < 1 - r ^ 2 := by nlinarith
  have hseg : uIcc x y ⊆ Icc (-r) r := uIcc_subset_Icc (abs_le.mp hx) (abs_le.mp hy)
  have hmem (z : ℝ) (hz : z ∈ uIcc x y) : z ∈ Ioo (-1 : ℝ) 1 := by
    have hh := hseg hz
    constructor <;> linarith [hh.1, hh.2]
  have hsmooth : ContDiffOn ℝ (3 : ℕ) Real.artanh (uIcc x y) :=
    fun z hz => (contDiffAt_artanh (hmem z hz) 3).contDiffWithinAt
  obtain ⟨z, hz, heq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (n := 2) hxy hsmooth
  have hu : UniqueDiffOn ℝ (uIcc x y) := uniqueDiffOn_Icc (by grind)
  have hxm := hmem x (left_mem_uIcc)
  have hw (k : ℕ) : iteratedDerivWithin k Real.artanh (uIcc x y) x =
      iteratedDeriv k Real.artanh x :=
    iteratedDerivWithin_eq_iteratedDeriv hu (contDiffAt_artanh hxm k) left_mem_uIcc
  have hp : taylorWithinEval Real.artanh 2 (uIcc x y) x y =
      Real.artanh x + (y - x) / (1 - x ^ 2) +
        x * (y - x) ^ 2 / (1 - x ^ 2) ^ 2 := by
    simp only [taylorWithinEval_succ, taylor_within_zero_eval, hw, iteratedDeriv_two hxm]
    norm_num
    rw [(hasDerivAt_artanh_interval hxm).deriv]
    ring
  have hzabs : |z| ≤ r := abs_le.mpr (hseg ⟨hz.1.le, hz.2.le⟩)
  have hC : 0 ≤ 8 / (1 - r ^ 2) ^ 3 := by positivity
  have hbound := abs_iteratedDeriv_three_le hr hzabs
  rw [hp] at heq
  norm_num at heq
  calc
    |Real.artanh y - Real.artanh x - (y - x) / (1 - x ^ 2) -
        x * (y - x) ^ 2 / (1 - x ^ 2) ^ 2| =
        |iteratedDeriv 3 Real.artanh z| * |y - x| ^ 3 / 6 := by
      have heq' : Real.artanh y - Real.artanh x - (y - x) / (1 - x ^ 2) -
          x * (y - x) ^ 2 / (1 - x ^ 2) ^ 2 =
          iteratedDeriv 3 Real.artanh z * (y - x) ^ 3 / 6 := by
        linarith [heq]
      rw [heq', abs_div, abs_mul, abs_pow]
      norm_num
    _ ≤ (8 / (1 - r ^ 2) ^ 3) * |y - x| ^ 3 / 6 := by gcongr
    _ ≤ (8 / (1 - r ^ 2) ^ 3) * |y - x| ^ 3 := by
      nlinarith [mul_nonneg hC (pow_nonneg (abs_nonneg (y - x)) 3)]

def remainder (x y : ℝ) : ℝ :=
  Real.artanh y - Real.artanh x - (y - x) / (1 - x ^ 2) -
    x * (y - x) ^ 2 / (1 - x ^ 2) ^ 2

theorem sum_remainder (x : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, remainder (x i) (x (i + 1))) =
      Real.artanh (x n) - Real.artanh (x 0) -
        (∑ i ∈ Finset.range n, (x (i + 1) - x i) / (1 - (x i) ^ 2)) -
        ∑ i ∈ Finset.range n,
          x i * (x (i + 1) - x i) ^ 2 / (1 - (x i) ^ 2) ^ 2 := by
  calc
    _ = (∑ i ∈ Finset.range n, (Real.artanh (x (i + 1)) - Real.artanh (x i))) -
        (∑ i ∈ Finset.range n, (x (i + 1) - x i) / (1 - (x i) ^ 2)) -
        ∑ i ∈ Finset.range n,
          x i * (x (i + 1) - x i) ^ 2 / (1 - (x i) ^ 2) ^ 2 := by
      simp only [remainder, Finset.sum_sub_distrib]
    _ = _ := by rw [Finset.sum_range_sub (fun i => Real.artanh (x i)) n]

theorem abs_sum_remainder_le {r δ : ℝ} (hr : r < 1)
    (x : ℕ → ℝ) (n : ℕ) (hx : ∀ i ≤ n, |x i| ≤ r)
    (hstep : ∀ i < n, |x (i + 1) - x i| ≤ δ) :
    |∑ i ∈ Finset.range n, remainder (x i) (x (i + 1))| ≤
      (8 / (1 - r ^ 2) ^ 3) * δ *
        ∑ i ∈ Finset.range n, (x (i + 1) - x i) ^ 2 := by
  have hr0 : 0 ≤ r := (abs_nonneg (x 0)).trans (hx 0 (Nat.zero_le n))
  have hrden : 0 < 1 - r ^ 2 := by nlinarith
  have hC : 0 ≤ 8 / (1 - r ^ 2) ^ 3 := by positivity
  calc
    _ ≤ ∑ i ∈ Finset.range n, |remainder (x i) (x (i + 1))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range n,
        (8 / (1 - r ^ 2) ^ 3) * δ * (x (i + 1) - x i) ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      have hin := Finset.mem_range.mp hi
      have hrem := abs_remainder_le hr (hx i hin.le) (hx (i + 1) hin)
      change |remainder (x i) (x (i + 1))| ≤ _ at hrem
      apply hrem.trans
      have hcubic : |x (i + 1) - x i| ^ 3 ≤ δ * (x (i + 1) - x i) ^ 2 := by
        rw [pow_succ, sq_abs]
        nlinarith [mul_le_mul_of_nonneg_left (hstep i hin) (sq_nonneg (x (i + 1) - x i))]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hcubic hC
    _ = _ := by rw [Finset.mul_sum]

theorem tendsto_sum_remainder {r q : ℝ} (hr : r < 1)
    (x : ℕ → ℕ → ℝ) (N : ℕ → ℕ) (δ : ℕ → ℝ)
    (hx : ∀ k i, i ≤ N k → |x k i| ≤ r)
    (hstep : ∀ k i, i < N k → |x k (i + 1) - x k i| ≤ δ k)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hquad : Tendsto (fun k => ∑ i ∈ Finset.range (N k),
      (x k (i + 1) - x k i) ^ 2) atTop (𝓝 q)) :
    Tendsto (fun k => ∑ i ∈ Finset.range (N k), remainder (x k i) (x k (i + 1)))
      atTop (𝓝 0) := by
  refine squeeze_zero_norm (a := fun k => (8 / (1 - r ^ 2) ^ 3) * δ k *
    ∑ i ∈ Finset.range (N k), (x k (i + 1) - x k i) ^ 2) ?_ ?_
  · intro k
    simpa only [Real.norm_eq_abs] using
      abs_sum_remainder_le hr (x k) (N k) (hx k) (hstep k)
  · simpa only [mul_zero, zero_mul] using
      (hδ.const_mul (8 / (1 - r ^ 2) ^ 3)).mul hquad

section Probability

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma measurable_remainder {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) :
    Measurable (fun ω => remainder (X ω) (Y ω)) := by
  unfold remainder Real.artanh
  fun_prop

theorem integrable_sum_remainder_and_bound {r : ℝ} (hr : r < 1)
    (x : ℕ → Ω → ℝ) (n : ℕ) (hm : ∀ i, Measurable (x i))
    (hx : ∀ᵐ ω ∂μ, ∀ i ≤ n, |x i ω| ≤ r)
    (hcube : ∀ i < n, Integrable (fun ω => |x (i + 1) ω - x i ω| ^ 3) μ) :
    Integrable (fun ω => ∑ i ∈ Finset.range n, remainder (x i ω) (x (i + 1) ω)) μ ∧
      (∫ ω, |∑ i ∈ Finset.range n, remainder (x i ω) (x (i + 1) ω)| ∂μ) ≤
        (8 / (1 - r ^ 2) ^ 3) *
          ∑ i ∈ Finset.range n, ∫ ω, |x (i + 1) ω - x i ω| ^ 3 ∂μ := by
  have hdom : Integrable (fun ω => (8 / (1 - r ^ 2) ^ 3) *
      ∑ i ∈ Finset.range n, |x (i + 1) ω - x i ω| ^ 3) μ :=
    (integrable_finsetSum _ (fun i hi => hcube i (Finset.mem_range.mp hi))).const_mul _
  have hrm : Measurable (fun ω => ∑ i ∈ Finset.range n,
      remainder (x i ω) (x (i + 1) ω)) :=
    Finset.measurable_fun_sum _ (fun i _ => measurable_remainder (hm i) (hm (i + 1)))
  have hb : ∀ᵐ ω ∂μ, |∑ i ∈ Finset.range n, remainder (x i ω) (x (i + 1) ω)| ≤
      (8 / (1 - r ^ 2) ^ 3) * ∑ i ∈ Finset.range n, |x (i + 1) ω - x i ω| ^ 3 := by
    filter_upwards [hx] with ω hω
    calc
      _ ≤ ∑ i ∈ Finset.range n, |remainder (x i ω) (x (i + 1) ω)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range n,
          (8 / (1 - r ^ 2) ^ 3) * |x (i + 1) ω - x i ω| ^ 3 := by
        apply Finset.sum_le_sum
        intro i hi
        have hin := Finset.mem_range.mp hi
        exact abs_remainder_le hr (hω i hin.le) (hω (i + 1) hin)
      _ = _ := by rw [Finset.mul_sum]
  have hi : Integrable (fun ω => ∑ i ∈ Finset.range n,
      remainder (x i ω) (x (i + 1) ω)) μ := by
    apply hdom.mono' hrm.aestronglyMeasurable
    simpa only [Real.norm_eq_abs] using hb
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ ω, (8 / (1 - r ^ 2) ^ 3) *
        ∑ i ∈ Finset.range n, |x (i + 1) ω - x i ω| ^ 3 ∂μ :=
      integral_mono_ae hi.abs hdom hb
    _ = _ := by
      rw [integral_const_mul, integral_finsetSum _
        (fun i hi => hcube i (Finset.mem_range.mp hi))]

theorem integrable_cube_of_localized [IsFiniteMeasure μ]
    {r : ℝ} {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hx : ∀ᵐ ω ∂μ, |X ω| ≤ r) (hy : ∀ᵐ ω ∂μ, |Y ω| ≤ r) :
    Integrable (fun ω => |Y ω - X ω| ^ 3) μ := by
  apply Integrable.of_bound ((hY.sub hX).abs.pow_const 3).aestronglyMeasurable ((2 * r) ^ 3)
  filter_upwards [hx, hy] with ω hxω hyω
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) 3)]
  have hd : |Y ω - X ω| ≤ 2 * r := by
    calc
      _ ≤ |Y ω| + |X ω| := abs_sub _ _
      _ ≤ _ := by linarith
  exact pow_le_pow_left₀ (abs_nonneg _) hd 3

theorem tendsto_integral_abs_sum_remainder [IsFiniteMeasure μ]
    {r : ℝ} (hr : r < 1) (x : ℕ → ℕ → Ω → ℝ) (N : ℕ → ℕ)
    (hm : ∀ k i, Measurable (x k i))
    (hx : ∀ k, ∀ᵐ ω ∂μ, ∀ i ≤ N k, |x k i ω| ≤ r)
    (hthird : Tendsto (fun k => ∑ i ∈ Finset.range (N k),
      ∫ ω, |x k (i + 1) ω - x k i ω| ^ 3 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ ω,
      |∑ i ∈ Finset.range (N k), remainder (x k i ω) (x k (i + 1) ω)| ∂μ)
      atTop (𝓝 0) := by
  have hb (k : ℕ) := integrable_sum_remainder_and_bound hr (x k) (N k) (hm k) (hx k)
    (fun i hi => integrable_cube_of_localized (hm k i) (hm k (i + 1))
      ((hx k).mono fun ω hω => hω i hi.le)
      ((hx k).mono fun ω hω => hω (i + 1) hi))
  apply squeeze_zero (fun k => integral_nonneg (fun ω => abs_nonneg _)) (fun k => (hb k).2)
  simpa only [mul_zero] using hthird.const_mul (8 / (1 - r ^ 2) ^ 3)

end Probability

end Problem367.ArtanhTaylor

end

end OAI
