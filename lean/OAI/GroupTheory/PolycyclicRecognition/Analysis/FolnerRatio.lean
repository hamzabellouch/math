import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! # Passing from a boundary estimate to a volume ratio -/

namespace PolycyclicRecognition

open Filter
open scoped Topology

theorem tendsto_ratio_one_of_boundary
    {ι : Type*} {l : Filter ι} (A N s b : ι → ℝ) {α β : ℝ}
    (hα : 0 < α) (hβ : 0 ≤ β)
    (hs : ∀ i, 0 < s i) (hb : ∀ i, 0 ≤ b i)
    (hlower : ∀ i, α * s i ≤ A i)
    (hmono : ∀ i, A i ≤ N i) (hupper : ∀ i, N i ≤ A i + β * b i)
    (hlim : Tendsto (fun i => b i / s i) l (𝓝 0)) :
    Tendsto (fun i => N i / A i) l (𝓝 1) := by
  have hA (i : ι) : 0 < A i := (mul_pos hα (hs i)).trans_le (hlower i)
  have hbound (i : ι) : N i / A i - 1 ≤ (β / α) * (b i / s i) := by
    calc
      N i / A i - 1 = (N i - A i) / A i := by field_simp [(hA i).ne']
      _ ≤ (β * b i) / A i :=
        div_le_div_of_nonneg_right (by linarith [hupper i]) (hA i).le
      _ ≤ (β * b i) / (α * s i) :=
        div_le_div_of_nonneg_left (mul_nonneg hβ (hb i)) (mul_pos hα (hs i)) (hlower i)
      _ = (β / α) * (b i / s i) := by ring
  have hz : Tendsto (fun i => N i / A i - 1) l (𝓝 0) := by
    apply squeeze_zero (fun i => sub_nonneg.mpr ((one_le_div (hA i)).mpr (hmono i))) hbound
    simpa only [mul_zero] using hlim.const_mul (β / α)
  simpa only [sub_add_cancel, zero_add] using hz.add_const 1

end PolycyclicRecognition

end OAI
