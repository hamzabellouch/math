import OAI.Geometry.RCD.Heat.HeatMassTail
import Mathlib.Topology.UniformSpace.UniformConvergence

namespace OAI

/-! # Uniform tail control from summable shell integrals -/

open Set Metric MeasureTheory Function Filter
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem integral_outside_dyadic_ball_le_integral_tail (μ : Measure X) (p : X)
    {r : ℝ} (hr : 0 < r) {f : X → ℝ} (hi : Integrable f μ)
    (hf : ∀ᵐ x ∂μ, 0 ≤ f x) {A : ℕ → ℝ}
    (hbound : ∀ j, (∫ x in dyadicShell p r j, f x ∂μ) ≤ A j)
    (hsum : Summable A) (N : ℕ) :
    (∫ x in (ball p (2 ^ N * r))ᶜ, f x ∂μ) ≤
      ∑' j, A (j + (N + 1)) := by
  let S := fun j => dyadicShell p r j ∩ (ball p (2 ^ N * r))ᶜ
  have hS (j : ℕ) : MeasurableSet (S j) :=
    (measurableSet_dyadicShell p r j).inter measurableSet_ball.compl
  have hdis : Pairwise (Disjoint on S) := by
    intro i j hij
    exact (disjoint_disjointed (fun j : ℕ => ball p (2 ^ j * r)) hij).mono
      inter_subset_left inter_subset_left
  have hUnion : (⋃ j, S j) = (ball p (2 ^ N * r))ᶜ := by
    rw [show (⋃ j, S j) = (⋃ j, dyadicShell p r j) ∩ (ball p (2 ^ N * r))ᶜ by
      ext x; simp only [S, mem_iUnion, mem_inter_iff, exists_and_right]]
    rw [iUnion_dyadicShell p hr, univ_inter]
  have hpart := hasSum_integral_iUnion hS hdis hi.integrableOn
  rw [hUnion] at hpart
  have hzero (j : ℕ) (hj : j ≤ N) : S j = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro x ⟨hx, hn⟩
    apply hn
    exact (ball_subset_ball (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj) hr.le))
      (dyadicShell_subset_ball p r j hx)
  have hpref : (∑ j ∈ Finset.range (N + 1), ∫ x in S j, f x ∂μ) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [hzero j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)), setIntegral_empty]
  have he := hpart.summable.sum_add_tsum_nat_add (N + 1)
  rw [hpref, zero_add, hpart.tsum_eq] at he
  rw [← he]
  apply ((summable_nat_add_iff (N + 1)).mpr hpart.summable).tsum_le_tsum _
    ((summable_nat_add_iff (N + 1)).mpr hsum)
  intro j
  have hle : (∫ x in S (j+(N+1)), f x ∂μ) ≤
      ∫ x in dyadicShell p r (j+(N+1)), f x ∂μ :=
    setIntegral_mono_set hi.integrableOn (ae_restrict_of_ae hf)
      (Eventually.of_forall fun _ hx => hx.1)
  exact hle.trans (hbound _)

theorem uniform_dyadic_integral_tails (μ : Measure X) (p : X)
    {r : ℝ} (hr : 0 < r) (F : Y → X → ℝ) (hi : ∀ y, Integrable (F y) μ)
    (hf : ∀ y, ∀ᵐ x ∂μ, 0 ≤ F y x) {A : ℕ → ℝ}
    (hbound : ∀ y j, (∫ x in dyadicShell p r j, F y x ∂μ) ≤ A j)
    (hsum : Summable A) :
    TendstoUniformly (fun N y => ∫ x in (ball p (2 ^ N * r))ᶜ, F y x ∂μ)
      (fun _ => 0) atTop := by
  have ht : Tendsto (fun N : ℕ => ∑' j, A (j+(N+1))) atTop (𝓝 0) :=
    (tendsto_sum_nat_add A).comp (tendsto_add_atTop_nat 1)
  apply Metric.tendstoUniformly_iff.mpr
  intro e he
  filter_upwards [ht.eventually_lt_const he] with N hN y
  have h0 : 0 ≤ ∫ x in (ball p (2 ^ N * r))ᶜ, F y x ∂μ :=
    integral_nonneg_of_ae (ae_restrict_of_ae (hf y))
  have hle := integral_outside_dyadic_ball_le_integral_tail μ p hr (hi y) (hf y)
    (hbound y) hsum N
  simpa only [dist_zero_left,Real.norm_eq_abs,abs_of_nonneg h0] using hle.trans_lt hN

end RegularPointCoordinates

end

end OAI
