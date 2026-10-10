import OAI.MathematicalPhysics.DefocusingNLS.Certificates.RectangleKernelNonzero

namespace OAI

/-! # The finite divisor has support strictly inside the counting rectangle -/

open Set Filter Function MeromorphicOn
open scoped Topology
namespace DefocusingNLS

theorem countingRectangle_subset_closed (V : ℝ) :
    countingRectangle V ⊆ closedCountingRectangle V := by
  rintro z ⟨h₁,h₂,h₃,h₄⟩
  exact ⟨h₁.le,h₂.le,h₃.le,h₄.le⟩

theorem closure_countingRectangle (V : ℝ) (hV : 0 < V) :
    closure (countingRectangle V) = closedCountingRectangle V := by
  have ho : countingRectangle V = Ioo (-(1/32 : ℝ)) 8 ×ℂ Ioo (-V) V := by
    ext z
    simp only [countingRectangle, mem_ofPred_eq, Complex.mem_reProdIm, mem_Ioo]
    tauto
  rw [ho, Complex.closure_reProdIm, closure_Ioo (by norm_num : -(1/32 : ℝ) ≠ 8),
    closure_Ioo (by linarith : -V ≠ V)]
  ext z
  simp only [closedCountingRectangle, mem_ofPred_eq, Complex.mem_reProdIm, mem_Icc]
  tauto

theorem counting_divisor_eq_orderNat (V : ℝ) (hV : 0 < V) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (closedCountingRectangle V))
    (hn : ∀ z ∈ countingRectangleBoundary V, f z ≠ 0)
    (z : ℂ) (hz : z ∈ closedCountingRectangle V) :
    MeromorphicOn.divisor f (closedCountingRectangle V) z = (analyticOrderNatAt f z : ℤ) := by
  rw [hf.divisor_apply hz,
    ← Nat.cast_analyticOrderNatAt (rectangle_analyticOrder_ne_top V hV f hf hn z hz)]
  simp

theorem counting_divisor_support_interior (V : ℝ) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (closedCountingRectangle V))
    (hn : ∀ z ∈ countingRectangleBoundary V, f z ≠ 0) :
    (MeromorphicOn.divisor f (closedCountingRectangle V)).support ⊆ countingRectangle V := by
  intro z hz
  have hc := (MeromorphicOn.divisor f (closedCountingRectangle V)).supportWithinDomain hz
  by_contra hi
  have ho := (hf z hc).analyticOrderAt_eq_zero.mpr (hn z ⟨hc, hi⟩)
  have he : MeromorphicOn.divisor f (closedCountingRectangle V) z = 0 := by
    rw [hf.divisor_apply hc, ho]
    simp
  exact hz he

theorem analytic_eqOn_of_rectangle_codiscrete (V : ℝ) (hV : 0 < V) (f g : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (closedCountingRectangle V))
    (hg : AnalyticOnNhd ℂ g (closedCountingRectangle V))
    (he : f =ᶠ[codiscreteWithin (closedCountingRectangle V)] g) :
    EqOn f g (closedCountingRectangle V) := by
  have h₀ := zero_mem_countingRectangle V hV
  have hc₀ := countingRectangle_subset_closed V h₀
  have he₀ := (eventuallyEq_codiscreteWithin_iff_forall_eventually_nhdsNE.mp he) 0 hc₀
  have hm₀ : ∀ᶠ z in 𝓝 (0 : ℂ), z ∈ countingRectangle V :=
    (isOpen_countingRectangle V).mem_nhds h₀
  have hm : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∈ closedCountingRectangle V :=
    (hm₀.filter_mono nhdsWithin_le_nhds).mono
      (fun _ hz => countingRectangle_subset_closed V hz)
  have heq : ∀ᶠ z in 𝓝[≠] (0 : ℂ), f z = g z := by
    filter_upwards [he₀, hm] with z he hz using he hz
  exact hf.eqOn_of_preconnected_of_frequently_eq hg
    (isConnected_closedCountingRectangle V hV).isPreconnected hc₀ heq.frequently

theorem rectangle_eqOn_deriv (V : ℝ) (hV : 0 < V) (f g : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (closedCountingRectangle V))
    (hg : AnalyticOnNhd ℂ g (closedCountingRectangle V))
    (he : EqOn f g (closedCountingRectangle V)) :
    EqOn (deriv f) (deriv g) (closedCountingRectangle V) := by
  have ho := (he.mono (countingRectangle_subset_closed V)).deriv (isOpen_countingRectangle V)
  apply ho.of_subset_closure hf.deriv.continuousOn hg.deriv.continuousOn
    (countingRectangle_subset_closed V)
  rw [closure_countingRectangle V hV]

end DefocusingNLS

end OAI
