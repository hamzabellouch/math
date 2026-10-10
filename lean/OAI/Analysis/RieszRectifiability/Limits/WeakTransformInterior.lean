import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.RieszInteriorCapError
import OAI.Analysis.RieszRectifiability.Kernel.CappedPairingSymmetrization

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Filter Topology
open scoped NNReal

theorem finite_capped_interior_tendsto {d : ℕ} (p : ℕ) (C : ℝ)
    (ν : Measure (Ambient d)) [IsFiniteMeasure ν] (hg : GlobalUpperGrowth (p + 1) C ν)
    (e : Ambient d) (φ : Ambient d → ℝ) (L B : ℝ≥0)
    (hφ : LipschitzWith L φ) (hB : ∀ x, |φ x| ≤ (B : ℝ))
    (ε : ℕ → ℝ) (hε : ∀ j, 0 < ε j) (hεlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun j => ∫ q, cappedRieszInterior (p + 1) (ε j) e φ q ∂ν.prod ν) atTop
      (𝓝 (∫ q, rieszInteriorIntegrand (p + 1) e φ q ∂ν.prod ν)) := by
  let A := (‖e‖ * (L : ℝ)) * (ν.real Set.univ * (2 * (C * 2 ^ (p + 1) * 2 ^ p)))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) (fun j => ?_)
    (show Tendsto (fun j => A * ε j) atTop (𝓝 0) by
      simpa only [mul_zero] using! hεlim.const_mul A)
  rw [Real.norm_eq_abs, abs_sub_comm]
  have h := (rieszInterior_integrable_and_cap_error p C ν hg e φ L B hφ hB (ε j) (hε j)).2
  calc
    _ ≤ (‖e‖ * (L : ℝ)) * (ν.real Set.univ * (2 * (C * 2 ^ (p + 1) * 2 ^ p * ε j))) := h
    _ = _ := by dsimp only [A]; ring

theorem weak_transform_represents_interior {d : ℕ} (p : ℕ) (C : ℝ)
    (ν : Measure (Ambient d)) [IsFiniteMeasure ν] (hg : GlobalUpperGrowth (p + 1) C ν)
    (e : Ambient d) (ε : ℕ → ℝ) (hε : ∀ j, 0 < ε j) (hεlim : Tendsto ε atTop (𝓝 0))
    (v : Lp ℝ 2 ν)
    (hweak : ∀ g : Ambient d → ℝ, MemLp g 2 ν →
      Tendsto (fun j => ∫ x, scalarCappedTransform (p + 1) ν e (ε j) (fun _ => 1) x * g x ∂ν)
        atTop (𝓝 (∫ x, v x * g x ∂ν)))
    (φ : Ambient d → ℝ) (L B : ℝ≥0) (hφ : LipschitzWith L φ)
    (hB : ∀ x, |φ x| ≤ (B : ℝ)) :
    (∫ x, v x * φ x ∂ν) = (1 / 2 : ℝ) * (∫ q, rieszInteriorIntegrand (p + 1) e φ q ∂ν.prod ν) := by
  have hφ₂ : MemLp φ 2 ν :=
    MemLp.of_bound hφ.continuous.aestronglyMeasurable B (Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using! hB x)
  have hφ₁ := hφ₂.integrable (by norm_num)
  have heq (j : ℕ) := finite_capped_pairing_symmetrization (p + 1) ν e (ε j) (hε j)
    φ hφ.continuous.measurable hφ₁
  have hlim : Tendsto (fun j => ∫ x, scalarCappedTransform (p + 1) ν e (ε j) (fun _ => 1) x * φ x ∂ν)
      atTop (𝓝 ((1 / 2 : ℝ) * (∫ q, rieszInteriorIntegrand (p + 1) e φ q ∂ν.prod ν))) := by
    simp only [heq]
    exact (finite_capped_interior_tendsto p C ν hg e φ L B hφ hB ε hε hεlim).const_mul (1 / 2 : ℝ)
  exact tendsto_nhds_unique (hweak φ hφ₂) hlim

end

end RieszRectifiability

end OAI
