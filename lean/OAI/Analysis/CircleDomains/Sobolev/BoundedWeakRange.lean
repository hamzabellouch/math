import OAI.Analysis.CircleDomains.Modulus.WeightedScalarTests
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

namespace OAI

/-! Weak L² limits of functions valued in the unit interval still lie in
that interval almost everywhere. The proof tests measurable sets. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

theorem ae_mem_unitInterval_of_weak_limit
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {u : ℕ → X → ℝ} (hm : ∀ n, AEStronglyMeasurable (u n) μ)
    (hb : ∀ n x, u n x ∈ Icc 0 1) (V : Lp ℝ 2 μ)
    (hw : ∀ w : Lp ℝ 2 μ, Tendsto (fun n => ∫ x, u n x * w x ∂μ)
      atTop (𝓝 (∫ x, V x * w x ∂μ))) :
    ∀ᵐ x ∂μ, V x ∈ Icc 0 1 := by
  have hi (n : ℕ) : Integrable (u n) μ := by
    apply MemLp.integrable (q := 2) (by norm_num)
    apply MemLp.of_bound (hm n) 1
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hb n x).1]
      exact (hb n x).2
  have hlim (s : Set X) (hs : MeasurableSet s) :
      Tendsto (fun n => ∫ x in s, u n x ∂μ) atTop (𝓝 (∫ x in s, V x ∂μ)) := by
    have he (f : X → ℝ) : (∫ x, f x * s.indicator (fun _ => (1 : ℝ)) x ∂μ) =
        ∫ x in s, f x ∂μ := by
      rw [← integral_indicator hs]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        by_cases hx : x ∈ s <;> simp [hx]
    simpa only [he] using tendsto_pairings_with_memLp_test hw
      (memLp_indicator_const 2 hs 1 (Or.inr (measure_ne_top μ s)))
  have hlo : ∀ᵐ x ∂μ, 0 ≤ V x := by
    apply ae_nonneg_of_forall_setIntegral_nonneg ((Lp.memLp V).integrable (by norm_num))
    intro s hs _
    exact le_of_tendsto_of_tendsto tendsto_const_nhds (hlim s hs)
      (Eventually.of_forall fun n => integral_nonneg (fun x => (hb n x).1))
  have hhi : ∀ᵐ x ∂μ, V x ≤ 1 := by
    apply ae_le_of_forall_setIntegral_le ((Lp.memLp V).integrable (by norm_num)) (integrable_const 1)
    intro s hs _
    apply le_of_tendsto_of_tendsto (hlim s hs) tendsto_const_nhds
    exact Eventually.of_forall fun n => integral_mono (hi n).integrableOn
      (integrable_const 1) (fun x => (hb n x).2)
  filter_upwards [hlo, hhi] with x hx hy
  exact ⟨hx, hy⟩

end CircleDomainRigidity

end

end OAI
