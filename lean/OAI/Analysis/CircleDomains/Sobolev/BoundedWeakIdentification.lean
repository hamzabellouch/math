import OAI.Analysis.CircleDomains.Modulus.WeightedScalarTests
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

/-! On a measurable region where uniformly bounded functions converge
pointwise, their L² weak limit has the same values almost everywhere. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

theorem ae_eq_on_of_bounded_weak_pointwise
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {u : ℕ → X → ℝ} (hm : ∀ n, AEStronglyMeasurable (u n) μ)
    (hb : ∀ n x, ‖u n x‖ ≤ 1) (V : Lp ℝ 2 μ)
    (hw : ∀ w : Lp ℝ 2 μ, Tendsto (fun n => ∫ x, u n x * w x ∂μ)
      atTop (𝓝 (∫ x, V x * w x ∂μ)))
    {s : Set X} (hs : MeasurableSet s) {t : X → ℝ}
    (ht : ∀ x ∈ s, ‖t x‖ ≤ 1)
    (hp : ∀ x ∈ s, Tendsto (fun n => u n x) atTop (𝓝 (t x))) :
    ∀ᵐ x ∂μ, x ∈ s → V x = t x := by
  let T := s.indicator t
  have hpm : ∀ᵐ x ∂μ, Tendsto (fun n => s.indicator (u n) x) atTop (𝓝 (T x)) := by
    apply Eventually.of_forall
    intro x
    by_cases hx : x ∈ s
    · simpa only [indicator_of_mem hx, T] using hp x hx
    · simp only [indicator_of_notMem hx, T]
      exact tendsto_const_nhds
  have hTm : AEStronglyMeasurable T μ :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hm n).indicator hs) hpm
  have hT : MemLp T 2 μ := MemLp.of_bound hTm 1 (Eventually.of_forall fun x => by
    by_cases hx : x ∈ s
    · simpa only [T, indicator_of_mem hx] using ht x hx
    · simp only [T, indicator_of_notMem hx, norm_zero, zero_le_one])
  let D := s.indicator (fun x => V x - T x)
  have hD : MemLp D 2 μ := ((Lp.memLp V).sub hT).indicator hs
  have hprod := tendsto_integral_of_dominated_convergence
    (F := fun n x => u n x * D x) (f := fun x => T x * D x) (fun x => ‖D x‖)
    (fun n => (hm n).mul hD.aestronglyMeasurable)
    (hD.integrable (by norm_num)).norm
    (fun n => Eventually.of_forall fun x => by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (hb n x) (norm_nonneg _)).trans_eq (one_mul _))
    (Eventually.of_forall fun x => by
      by_cases hx : x ∈ s
      · simpa only [T, indicator_of_mem hx] using (hp x hx).mul_const (D x)
      · simp only [D, T, indicator_of_notMem hx, mul_zero]
        exact tendsto_const_nhds)
  have he := tendsto_nhds_unique (tendsto_pairings_with_memLp_test hw hD) hprod
  have hI₁ : Integrable (fun x => V x * D x) μ := (Lp.memLp V).integrable_mul hD
  have hI₂ : Integrable (fun x => T x * D x) μ := hT.integrable_mul hD
  have hint : (∫ x, (V x - T x) * D x ∂μ) = 0 := by
    rw [show (fun x => (V x - T x) * D x) =
      (fun x => V x * D x - T x * D x) from funext (fun x => sub_mul _ _ _),
      integral_sub hI₁ hI₂]
    exact sub_eq_zero.mpr he
  have hDD : (fun x => (V x - T x) * D x) = fun x => D x ^ 2 := by
    funext x
    by_cases hx : x ∈ s <;> simp [D, hx, pow_two]
  rw [hDD] at hint
  have hzero := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (D x)) hD.integrable_sq).mp hint
  filter_upwards [hzero] with x hx hxs
  have hDx : D x = 0 := sq_eq_zero_iff.mp hx
  simpa only [D, T, indicator_of_mem hxs, sub_eq_zero] using hDx

end CircleDomainRigidity

end

end OAI
