import Mathlib
import OAI.Analysis.Conductivity.Model

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity
open MeasureTheory Set Filter Topology
open scoped ENNReal

lemma Lp_elliptic_bounds
    {X V : Type*} [MeasurableSpace X] [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
    (μ : Measure X) (E F : Lp V 2 μ) {a b : ℝ} (_ha : 0 < a) (hb : 0 ≤ b)
    (h : ∀ᵐ x ∂μ, a * ‖E x‖^2 ≤ inner ℝ (E x) (F x) ∧
      ‖F x‖^2 ≤ b^2 * ‖E x‖^2) :
    a * ‖E‖^2 ≤ inner ℝ E F ∧ ‖F‖ ≤ b * ‖E‖ := by
  constructor
  · rw [← real_inner_self_eq_norm_sq,L2.inner_def,L2.inner_def,← integral_const_mul]
    apply integral_mono_ae ((L2.integrable_inner E E).const_mul a) (L2.integrable_inner E F)
    filter_upwards [h] with x hx
    simpa only [real_inner_self_eq_norm_sq] using hx.1
  · have hn : ∀ᵐ x ∂μ, ‖F x‖ ≤ ‖b • E x‖ := by
      filter_upwards [h] with x hx
      rw [norm_smul,Real.norm_of_nonneg hb]
      nlinarith [norm_nonneg (F x), norm_nonneg (E x),mul_nonneg hb (norm_nonneg (E x))]
    have hLp : ∀ᵐ x ∂μ, ‖F x‖ ≤ ‖(b • E : Lp V 2 μ) x‖ := by
      filter_upwards [hn,Lp.coeFn_smul b E] with x hx hy
      simpa only [hy,Pi.smul_apply] using hx
    have hp := Lp.norm_le_norm_of_ae_le hLp
    simpa only [norm_smul,Real.norm_of_nonneg hb] using hp

lemma elliptic_energy_bound
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (E F E₀ : H) {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hell : a * ‖E‖^2 ≤ inner ℝ E F) (hflux : ‖F‖ ≤ b * ‖E‖)
    (horth : inner ℝ (E-E₀) F = 0) :
    ‖E‖ ≤ (b/a) * ‖E₀‖ ∧ ‖F‖ ≤ (b^2/a) * ‖E₀‖ := by
  have he : inner ℝ E F = inner ℝ E₀ F := by
    rw [inner_sub_left] at horth
    linarith
  have hi : a * ‖E‖^2 ≤ ‖E₀‖ * (b * ‖E‖) := by
    calc
      _ ≤ inner ℝ E₀ F := he ▸ hell
      _ ≤ ‖E₀‖ * ‖F‖ := real_inner_le_norm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hflux (norm_nonneg _)
  have hbound : ‖E‖ ≤ (b/a) * ‖E₀‖ := by
    by_cases hz : ‖E‖ = 0
    · rw [hz]; positivity
    · have hp : 0 < ‖E‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
      have hh : a * ‖E‖ ≤ b * ‖E₀‖ := by nlinarith
      have hd : ‖E‖ ≤ (b * ‖E₀‖) / a := (le_div_iff₀ ha).mpr (by nlinarith)
      convert hd using 1; ring
  refine ⟨hbound,hflux.trans ?_⟩
  calc
    _ ≤ b * ((b/a)*‖E₀‖) := mul_le_mul_of_nonneg_left hbound hb
    _ = (b^2/a)*‖E₀‖ := by ring

end ScalarConductivity

end

end OAI
