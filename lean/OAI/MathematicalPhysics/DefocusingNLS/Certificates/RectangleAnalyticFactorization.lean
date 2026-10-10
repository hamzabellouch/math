import OAI.MathematicalPhysics.DefocusingNLS.Certificates.RectangleRoucheInput
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Meromorphic.FactorizedRational

namespace OAI

/-! # Finite analytic divisors in the one counting rectangle -/

open Set Filter Function
namespace DefocusingNLS

theorem convex_closedCountingRectangle (V : ℝ) : Convex ℝ (closedCountingRectangle V) := by
  change Convex ℝ ({z : ℂ | -(1 / 32 : ℝ) ≤ z.re} ∩
    ({z : ℂ | z.re ≤ 8} ∩ ({z : ℂ | -V ≤ z.im} ∩ {z : ℂ | z.im ≤ V})))
  exact (convex_halfSpace_re_ge _).inter ((convex_halfSpace_re_le _).inter
    ((convex_halfSpace_im_ge _).inter (convex_halfSpace_im_le _)))

theorem isConnected_closedCountingRectangle (V : ℝ) (hV : 0 < V) :
    IsConnected (closedCountingRectangle V) := by
  apply (convex_closedCountingRectangle V).isConnected
  refine ⟨0, ?_⟩
  simp only [closedCountingRectangle, mem_ofPred_eq, Complex.zero_re, Complex.zero_im]
  constructor
  · norm_num
  exact ⟨by norm_num, by linarith, hV.le⟩

theorem eight_mem_countingRectangleBoundary (V : ℝ) (hV : 0 < V) :
    (8 : ℂ) ∈ countingRectangleBoundary V := by
  rw [mem_countingRectangleBoundary_iff]
  constructor
  · change -(1 / 32 : ℝ) ≤ 8 ∧ (8 : ℝ) ≤ 8 ∧ -V ≤ 0 ∧ (0 : ℝ) ≤ V
    exact ⟨by norm_num, le_rfl, by linarith, hV.le⟩
  · exact Or.inr (Or.inl rfl)

theorem rectangle_analyticOrder_ne_top (V : ℝ) (hV : 0 < V) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (closedCountingRectangle V))
    (hn : ∀ z ∈ countingRectangleBoundary V, f z ≠ 0) :
    ∀ z ∈ closedCountingRectangle V, analyticOrderAt f z ≠ ⊤ := by
  have hz := eight_mem_countingRectangleBoundary V hV
  have ho : analyticOrderAt f (8 : ℂ) = 0 := (hf _ hz.1).analyticOrderAt_eq_zero.mpr (hn _ hz)
  have hall := (hf.exists_analyticOrderAt_ne_top_iff_forall
    (isConnected_closedCountingRectangle V hV)).mp
      ⟨⟨8, hz.1⟩, by rw [ho]; exact ENat.zero_ne_top⟩
  exact fun z hz => hall ⟨z, hz⟩

theorem rectangle_extract_zeros (V : ℝ) (hV : 0 < V) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (closedCountingRectangle V))
    (hn : ∀ z ∈ countingRectangleBoundary V, f z ≠ 0) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (closedCountingRectangle V) ∧
      (∀ z ∈ closedCountingRectangle V, g z ≠ 0) ∧
      f =ᶠ[codiscreteWithin (closedCountingRectangle V)]
        (∏ᶠ z, (· - z) ^ MeromorphicOn.divisor f (closedCountingRectangle V) z) • g := by
  have ho := rectangle_analyticOrder_ne_top V hV f hf hn
  have hm : ∀ z : closedCountingRectangle V, meromorphicOrderAt f z ≠ ⊤ := by
    intro z
    rw [(hf z z.2).meromorphicOrderAt_eq]
    simpa using ho z z.2
  obtain ⟨g, hg, hgn, he⟩ := hf.meromorphicOn.extract_zeros_poles hm
    ((MeromorphicOn.divisor f (closedCountingRectangle V)).finiteSupport
      (isCompact_closedCountingRectangle V))
  exact ⟨g, hg, fun z hz => hgn ⟨z, hz⟩, he⟩

end DefocusingNLS

end OAI
