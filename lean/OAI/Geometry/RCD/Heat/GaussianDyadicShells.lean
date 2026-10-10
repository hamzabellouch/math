import OAI.Geometry.RCD.Heat.GaussianOffDiagonal
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Order.Disjointed

namespace OAI

/-! # Dyadic shell integration and Gaussian summability -/

open Set Metric MeasureTheory Filter
open scoped Topology

noncomputable section

namespace RegularPointCoordinates

/-- A geometric volume or normalization loss is summable against the
Gaussian decay on dyadic annuli. -/
theorem summable_dyadic_gaussian {b c d : ℝ} (hb : 0 ≤ b) (hc : 0 < c) (hd : 1 < d) :
    Summable (fun j : ℕ => b ^ j * Real.exp (-c * d ^ j)) := by
  have hg : 0 < c * (d - 1) := mul_pos hc (sub_pos.mpr hd)
  have ht := Real.tendsto_exp_neg_atTop_nhds_zero.comp
    ((tendsto_pow_atTop_atTop_of_one_lt hd).const_mul_atTop hg)
  have ht' : Tendsto (fun j : ℕ => b * Real.exp (-(c * (d - 1)) * d ^ j))
      atTop (𝓝 0) := by
    simpa only [Function.comp_apply, neg_mul, mul_zero] using ht.const_mul b
  apply summable_of_ratio_norm_eventually_le (r := 1 / 2) (by norm_num)
  filter_upwards [ht'.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2)] with j hj
  have he : b ^ (j + 1) * Real.exp (-c * d ^ (j + 1)) =
      (b * Real.exp (-(c * (d - 1)) * d ^ j)) *
        (b ^ j * Real.exp (-c * d ^ j)) := by
    rw [pow_succ, pow_succ]
    calc
      _ = (b * b ^ j) * Real.exp (-(c * (d - 1)) * d ^ j + -c * d ^ j) := by
        have hexp : -c * (d ^ j * d) =
            -(c * (d - 1)) * d ^ j + -c * d ^ j := by ring
        rw [hexp]
        ring
      _ = _ := by rw [Real.exp_add]; ring
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (pow_nonneg hb _) (Real.exp_pos _).le),
    abs_of_nonneg (mul_nonneg (pow_nonneg hb _) (Real.exp_pos _).le), he]
  exact mul_le_mul_of_nonneg_right hj (mul_nonneg (pow_nonneg hb _) (Real.exp_pos _).le)

variable {X : Type*} [MetricSpace X]

/-- Disjoint dyadic balls, including the initial ball at index zero. -/
def dyadicShell (p : X) (r : ℝ) (j : ℕ) : Set X :=
  disjointed (fun i : ℕ => ball p (2 ^ i * r)) j

theorem dyadicShell_subset_ball (p : X) (r : ℝ) (j : ℕ) :
    dyadicShell p r j ⊆ ball p (2 ^ j * r) :=
  disjointed_subset _ j

theorem iUnion_dyadicShell (p : X) {r : ℝ} (hr : 0 < r) :
    (⋃ j : ℕ, dyadicShell p r j) = univ := by
  simp only [dyadicShell, iUnion_disjointed]
  apply eq_univ_of_forall
  intro x
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (dist x p / r) (by norm_num : (1 : ℝ) < 2)
  exact mem_iUnion.mpr ⟨j, (div_lt_iff₀ hr).mp hj⟩

theorem dyadicShell_separation (p : X) {r : ℝ} (hr : 0 < r) (j : ℕ)
    {x : X} (hx : x ∈ dyadicShell p r (j + 1)) : 2 ^ j * r ≤ dist x p := by
  have hm : Monotone (fun i : ℕ => ball p (2 ^ i * r)) := by
    intro i k hik
    exact ball_subset_ball (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hik) hr.le)
  change x ∈ disjointed (fun i : ℕ => ball p (2 ^ i * r)) (Order.succ j) at hx
  rw [hm.disjointed_succ (by simp)] at hx
  exact le_of_not_gt hx.2

variable [MeasurableSpace X] [BorelSpace X]

@[measurability]
theorem measurableSet_dyadicShell (p : X) (r : ℝ) (j : ℕ) :
    MeasurableSet (dyadicShell p r j) :=
  MeasurableSet.disjointed (fun _ => measurableSet_ball) j

/-- A weighted integral is bounded by a series of ball error budgets.
The kernel bound is only needed on each disjoint shell. -/
theorem integral_le_dyadic_shell_sum_of_product (μ : Measure X) (p : X) {r : ℝ} (hr : 0 < r)
    {f w : X → ℝ} {W e : ℕ → ℝ}
    (hi : Integrable (fun x => w x * f x) μ)
    (hfi : ∀ j, IntegrableOn f (ball p (2 ^ j * r)) μ)
    (hf : ∀ᵐ x ∂μ, 0 ≤ f x) (hW : ∀ j, 0 ≤ W j)
    (hw : ∀ j, ∀ᵐ x ∂μ.restrict (dyadicShell p r j), w x * f x ≤ W j * f x)
    (he : ∀ j, (∫ x in ball p (2 ^ j * r), f x ∂μ) ≤ e j)
    (hsum : Summable (fun j => W j * e j)) :
    (∫ x, w x * f x ∂μ) ≤ ∑' j : ℕ, W j * e j := by
  have hpart := hasSum_integral_iUnion (fun j => measurableSet_dyadicShell p r j)
    (disjoint_disjointed _) hi.integrableOn
  rw [iUnion_dyadicShell p hr, setIntegral_univ] at hpart
  rw [← hpart.tsum_eq]
  apply hpart.summable.tsum_le_tsum _ hsum
  intro j
  have hsub := dyadicShell_subset_ball p r j
  have hlocal : (∫ x in dyadicShell p r j, w x * f x ∂μ) ≤
      W j * ∫ x in dyadicShell p r j, f x ∂μ := by
    rw [← integral_const_mul]
    apply integral_mono_ae hi.integrableOn (((hfi j).mono_set hsub).const_mul (W j))
    exact hw j
  have hball : (∫ x in dyadicShell p r j, f x ∂μ) ≤
      ∫ x in ball p (2 ^ j * r), f x ∂μ :=
    setIntegral_mono_set (hfi j) (ae_restrict_of_ae hf)
      (Filter.Eventually.of_forall fun _ hx => hsub hx)
  exact hlocal.trans (mul_le_mul_of_nonneg_left (hball.trans (he j)) (hW j))

end RegularPointCoordinates

end

end OAI
