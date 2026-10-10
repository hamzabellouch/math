import Mathlib
import OAI.Geometry.TamingCompatibility.Functional.QuadraticShell

namespace OAI

section
section

section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace QuadraticShell

lemma lintegral_profile_le_series {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) (δ : Y → ℝ≥0∞) (hδ : Measurable δ) {r : ℝ} (hr : 0 < r) :
    ∫⁻ y, profile r (δ y) ∂μ ≤ ∑' n : ℕ,
      ENNReal.ofReal ((1/64:ℝ)^n) * μ {y | δ y < ENNReal.ofReal (2^(n+1)*r)} := by
  let f : ℕ → Y → ℝ≥0∞ := fun n =>
    {y | δ y < ENNReal.ofReal (2^(n+1)*r)}.indicator
      (fun _ => ENNReal.ofReal ((1/64:ℝ)^n))
  have hf : ∀ n, Measurable (f n) := fun n =>
    measurable_const.indicator (measurableSet_lt hδ measurable_const)
  calc
    _ ≤ ∫⁻ y, ∑' n, f n y ∂μ := lintegral_mono fun y => profile_majorant hr (δ y)
    _ = ∑' n, ∫⁻ y, f n y ∂μ := lintegral_tsum fun n => (hf n).aemeasurable
    _ = _ := by congr 1; funext n; exact lintegral_indicator_const (measurableSet_lt hδ measurable_const) _

def dyadicMass {Y : Type*} [MeasurableSpace Y] (μ : Measure Y)
    (δ : Y → ℝ≥0∞) (r : ℝ) (n : ℕ) : ℝ :=
  (1/64:ℝ)^n * μ.real {y | δ y < ENNReal.ofReal (2^(n+1)*r)} / r^2

lemma dyadicMass_nonneg {Y : Type*} [MeasurableSpace Y] (μ : Measure Y)
    (δ : Y → ℝ≥0∞) (r : ℝ) (n : ℕ) : 0 ≤ dyadicMass μ δ r n := by
  unfold dyadicMass; positivity

lemma dyadicMass_bound {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) (δ : Y → ℝ≥0∞) (C : ℝ)
    (hgrowth : ∀ s : ℝ, 0 < s → μ.real {y | δ y < ENNReal.ofReal s} ≤ C*s^2)
    {r : ℝ} (hr : 0 < r) (n : ℕ) :
    dyadicMass μ δ r n ≤ 4*C*(1/16:ℝ)^n := by
  unfold dyadicMass
  calc
    _ ≤ (1/64:ℝ)^n * (C*(2^(n+1)*r)^2) / r^2 := by
      gcongr
      exact hgrowth _ (by positivity)
    _ = _ := by rw [dyadic_term_identity]; field_simp

lemma normalized_profile_le_tsum {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ] (δ : Y → ℝ≥0∞) (hδ : Measurable δ)
    {r : ℝ} (hr : 0 < r) (hsum : Summable (dyadicMass μ δ r)) :
    (∫⁻ y, profile r (δ y) ∂μ).toReal / r^2 ≤ ∑' n, dyadicMass μ δ r n := by
  have heq : (∑' n : ℕ,
      ENNReal.ofReal ((1/64:ℝ)^n) * μ {y | δ y < ENNReal.ofReal (2^(n+1)*r)}) =
      ENNReal.ofReal (r^2*(∑' n, dyadicMass μ δ r n)) := by
    rw [ENNReal.ofReal_mul (sq_nonneg r), ENNReal.ofReal_tsum_of_nonneg
      (dyadicMass_nonneg μ δ r) hsum, ← ENNReal.tsum_mul_left]
    congr 1; funext n
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ _), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (sq_nonneg r)]
    apply congrArg ENNReal.ofReal
    change _ = r^2*((1/64:ℝ)^n*μ.real _/r^2)
    field_simp
    rfl
  have hle := (lintegral_profile_le_series μ δ hδ hr).trans_eq heq
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
  rw [ENNReal.toReal_ofReal (mul_nonneg (sq_nonneg r)
    (tsum_nonneg (dyadicMass_nonneg μ δ r)))] at hreal
  exact (div_le_iff₀ (sq_pos_of_pos hr)).mpr (by simpa [mul_comm] using hreal)

lemma dyadicMass_tendsto_zero {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) (δ : Y → ℝ≥0∞)
    (hzero : Tendsto (fun r : ℝ => μ.real {y | δ y < ENNReal.ofReal r}/r^2)
      (𝓝[>] (0:ℝ)) (𝓝 0)) (n : ℕ) :
    Tendsto (fun r : ℝ => dyadicMass μ δ r n) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have ht : Tendsto (fun r : ℝ => 2^(n+1)*r) (𝓝[>] (0:ℝ)) (𝓝[>] (0:ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_,?_⟩
    · simpa using (tendsto_const_nhds.mul nhdsWithin_le_nhds :
        Tendsto (fun r : ℝ => 2^(n+1)*r) (𝓝[>] (0:ℝ)) (𝓝 (2^(n+1)*0)))
    · filter_upwards [self_mem_nhdsWithin] with r hr
      change 0 < 2^(n+1)*r
      exact mul_pos (by positivity) hr
  have h := (hzero.comp ht).const_mul ((1/64:ℝ)^n*(2^(n+1))^2)
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  dsimp [dyadicMass,Function.comp_def]
  field_simp

theorem normalized_profile_tendsto_zero {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ] (δ : Y → ℝ≥0∞) (hδ : Measurable δ)
    (C : ℝ) (_hC : 0 ≤ C)
    (hgrowth : ∀ s : ℝ, 0 < s → μ.real {y | δ y < ENNReal.ofReal s} ≤ C*s^2)
    (hzero : Tendsto (fun r : ℝ => μ.real {y | δ y < ENNReal.ofReal r}/r^2)
      (𝓝[>] (0:ℝ)) (𝓝 0)) :
    Tendsto (fun r : ℝ => (∫⁻ y, profile r (δ y) ∂μ).toReal/r^2)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hs : Summable (fun n : ℕ => 4*C*(1/16:ℝ)^n) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1/16:ℝ)‖<1)).mul_left _
  have hb : ∀ᶠ r in 𝓝[>] (0:ℝ), ∀ n : ℕ,
      ‖dyadicMass μ δ r n‖ ≤ 4*C*(1/16:ℝ)^n := by
    filter_upwards [self_mem_nhdsWithin] with r hr n
    rw [Real.norm_of_nonneg (dyadicMass_nonneg μ δ r n)]
    exact dyadicMass_bound μ δ C hgrowth hr n
  have hlim := tendsto_tsum_of_dominated_convergence hs
    (dyadicMass_tendsto_zero μ δ hzero) hb
  simp only [tsum_zero] at hlim
  apply squeeze_zero' ?_ ?_ hlim
  · filter_upwards [] with r; positivity
  · filter_upwards [self_mem_nhdsWithin,hb] with r hr hbr
    exact normalized_profile_le_tsum μ δ hδ hr (hs.of_norm_bounded hbr)

end QuadraticShell

end
end

section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace QuadraticShell

lemma profile_le_one (r : ℝ) (d : ℝ≥0∞) : profile r d ≤ 1 := by
  apply pow_le_one₀ bot_le
  exact ENNReal.inv_le_one.mpr le_self_add

lemma measurable_profile {Y : Type*} [MeasurableSpace Y]
    (δ : Y → ℝ≥0∞) (hδ : Measurable δ) (r : ℝ) :
    Measurable (fun y => profile r (δ y)) := by
  unfold profile
  fun_prop

lemma integral_profile_toReal {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) (δ : Y → ℝ≥0∞) (hδ : Measurable δ) (r : ℝ) :
    (∫ y, (profile r (δ y)).toReal ∂μ) = (∫⁻ y, profile r (δ y) ∂μ).toReal := by
  exact integral_toReal (measurable_profile δ hδ r).aemeasurable
    (Eventually.of_forall fun y => (profile_le_one r (δ y)).trans_lt (by simp))

lemma integral_profile_normalized_bound {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ] (δ : Y → ℝ≥0∞) (hδ : Measurable δ)
    (C : ℝ) (hC : 0 ≤ C)
    (hgrowth : ∀ s : ℝ, 0 < s → μ.real {y | δ y < ENNReal.ofReal s} ≤ C*s^2)
    {r : ℝ} (hr : 0 < r) : (∫ y, (profile r (δ y)).toReal ∂μ)/r^2 ≤ 8*C := by
  rw [integral_profile_toReal μ δ hδ r]
  have hle := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (lintegral_profile_le μ δ hδ C hC hgrowth hr)
  rw [ENNReal.toReal_ofReal (by positivity)] at hle
  exact (div_le_iff₀ (sq_pos_of_pos hr)).mpr hle

lemma integral_profile_normalized_zero {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ] (δ : Y → ℝ≥0∞) (hδ : Measurable δ)
    (C : ℝ) (hC : 0 ≤ C)
    (hgrowth : ∀ s : ℝ, 0 < s → μ.real {y | δ y < ENNReal.ofReal s} ≤ C*s^2)
    (hzero : Tendsto (fun r : ℝ => μ.real {y | δ y < ENNReal.ofReal r}/r^2)
      (𝓝[>] (0:ℝ)) (𝓝 0)) :
    Tendsto (fun r : ℝ => (∫ y, (profile r (δ y)).toReal ∂μ)/r^2)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  simp_rw [integral_profile_toReal μ δ hδ]
  exact normalized_profile_tendsto_zero μ δ hδ C hC hgrowth hzero

end QuadraticShell

end
end

end
end

end OAI
