import OAI.Analysis.RCDHeat.ExistingAnalytic

namespace OAI

/-! # Strong L2 convergence of bounded functions with common finite support -/

open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem compact_supported_L2_limit {s : Set X} (hs : MeasurableSet s)
    (hfin : μ s ≠ ∞) (u : ℕ → Lp ℝ 2 μ) (v : Lp ℝ 2 μ)
    (F : ℕ → X → ℝ) (f : X → ℝ)
    (hu : ∀ k, u k =ᵐ[μ] F k) (hv : v =ᵐ[μ] f)
    {A : ℝ} (hA : 0 ≤ A) (hF : ∀ k x, |F k x| ≤ A)
    (hf : ∀ x, |f x| ≤ A)
    (hF0 : ∀ k x, x ∉ s → F k x = 0) (hf0 : ∀ x, x ∉ s → f x = 0)
    (hc : ∀ x ∈ s, Tendsto (fun k => F k x) atTop (𝓝 (f x))) :
    Tendsto u atTop (𝓝 v) := by
  let B := s.indicator (fun _ : X => (2*A)^2)
  have hB : Integrable B μ := by
    apply (integrable_indicator_iff hs).mpr
    exact integrableOn_const hfin
  have he : ∀ᵐ x ∂μ, (∀ k, u k x = F k x) ∧ v x = f x :=
    (ae_all_iff.mpr hu).and hv
  have hb : ∀ᶠ k in atTop, ∀ᵐ x ∂μ, (u k x-v x)^2 ≤ B x := by
    apply Eventually.of_forall
    intro k
    filter_upwards [he] with x hx
    rw [hx.1 k,hx.2]
    by_cases hxs : x ∈ s
    · dsimp only [B]
      rw [indicator_of_mem hxs]
      have hh := (abs_sub (F k x) (f x)).trans (add_le_add (hF k x) (hf x))
      nlinarith [sq_abs (F k x-f x),abs_nonneg (F k x-f x)]
    · simp only [B,indicator_of_notMem hxs,hF0 k x hxs,hf0 x hxs,sub_self,
        zero_pow (by norm_num : 2 ≠ 0),le_refl]
  have ht : ∀ᵐ x ∂μ, Tendsto (fun k => u k x) atTop (𝓝 (v x)) := by
    filter_upwards [he] with x hx
    simp only [hx.1,hx.2]
    by_cases hxs : x ∈ s
    · exact hc x hxs
    · simp only [hF0 _ x hxs,hf0 x hxs]
      exact tendsto_const_nhds
  have hh := L2Differentiation.toLp_tendsto_of_dominated μ (fun k => Lp.memLp (u k)) (Lp.memLp v) B hB hb ht
  simpa only [Lp.toLp_coeFn] using hh

end RegularPointCoordinates

end

end OAI
