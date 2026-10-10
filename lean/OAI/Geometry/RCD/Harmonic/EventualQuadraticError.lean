import OAI.Geometry.RCD.Harmonic.QuantitativeQuadraticMean
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

namespace OAI

/-! # Square-root errors from uniform Young estimates

The free Young parameter may be chosen after the mass budget. The choice
also works when the limiting mass is zero.
-/

open Set Filter
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

theorem eventual_error_le_sqrt {Y : Type*} (f : ℕ → Y → ℝ)
    {C V M B : ℝ} (hB : 0≤B)
    (h : ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop, ∀ y (a : ℝ), 0<a →
      4*a*|f k y|≤C*(4*a^2*V+M*(B+δ))) {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ k in atTop, ∀ y, |f k y|≤C*(V+M/4)*Real.sqrt (B+δ) := by
  let a := Real.sqrt (B+δ)
  have ha : 0<a := Real.sqrt_pos.mpr (by linarith)
  have hs : a^2=B+δ := Real.sq_sqrt (by linarith)
  have he : C*(4*a^2*V+M*(B+δ))=(4*a)*(C*(V+M/4)*a) := by
    rw [← hs]
    ring
  filter_upwards [h δ hδ] with k hk y
  have hh := hk y a ha
  rw [he] at hh
  exact (mul_le_mul_iff_right₀ (show 0<4*a by positivity)).mp hh

theorem eventual_error_le_sqrt_add {Y : Type*} (f : ℕ → Y → ℝ)
    {C V M B : ℝ} (hB : 0≤B)
    (h : ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop, ∀ y (a : ℝ), 0<a →
      4*a*|f k y|≤C*(4*a^2*V+M*(B+δ))) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ k in atTop, ∀ y, |f k y|≤C*(V+M/4)*Real.sqrt B+ε := by
  let δ (j : ℕ) : ℝ := 1/((j:ℝ)+1)
  have hδ j : 0<δ j := by dsimp only [δ]; positivity
  have hz : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hs := ((tendsto_const_nhds (x := B)).add hz).sqrt.const_mul (C*(V+M/4))
  simp only [add_zero] at hs
  obtain ⟨j,hj⟩ := (hs.eventually (gt_mem_nhds (show
    C*(V+M/4)*Real.sqrt B<C*(V+M/4)*Real.sqrt B+ε by linarith))).exists
  filter_upwards [eventual_error_le_sqrt f hB h (hδ j)] with k hk y
  exact (hk y).trans hj.le

end RegularPointCoordinates

end

end OAI
