import Mathlib
import OAI.Analysis.RieszRectifiability.Rigidity.LocalReflectionlessTransform
import OAI.Analysis.RieszRectifiability.Limits.IsometricWeakTransform
import OAI.Analysis.RieszRectifiability.Foundations.UnweightedCappedEquation

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem exists_source_planar_unweighted_capped_equation {d : ℕ} (p : ℕ) (C G : ℝ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hgrowth : ∀ j, GlobalUpperGrowth (p + 1) C (μ j))
    (hgν : GlobalUpperGrowth (p + 1) G ν) (hweak : CompactTestConvergence μ ν)
    (D : ℝ≥0)
    (hB : ∀ j ε, 0 < ε → ∀ f : Ambient d → ℝ, MemLp f 2 (μ j) →
      MemLp (truncated (p + 1) (μ j) ε f) 2 (μ j) ∧
        eLpNorm (truncated (p + 1) (μ j) ε f) 2 (μ j) ≤ (D : ℝ≥0∞) * eLpNorm f 2 (μ j))
    (L : Ambient (p + 1) →ₗᵢ[ℝ] Ambient d) (f : Ambient (p + 1) → ℝ)
    (hf : Measurable f) (c : ℝ) (hc : 0 < c) (hlower : ∀ x, c ≤ f x)
    (hdensity : ((volume : Measure (Ambient (p + 1))).withDensity
      (fun x => ENNReal.ofReal (f x))).map L = ν)
    (e a : Ambient (p + 1)) (H R : ℝ) (hH : 0 < H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hboundary : ν (frontier (ball (L a) R)) = 0) (hmass : ν (ball (L a) R) ≠ 0)
    (cMass : ℝ) (hcMass : 0 < cMass)
    (hlowerMass : ENNReal.ofReal (cMass * (H / 4) ^ (p + 1)) ≤ ν (ball (L a) (H / 4)))
    (hreflect : ScalarReflectionlessAt (p + 1) ν (L a)) :
    ∃ s : ℕ → ℕ, StrictMono s ∧
      Tendsto (fun j => (1 / 2 : ℝ) ^ (s j)) atTop (𝓝 0) ∧
      ∃ b : ℝ, ∀ (g : Ambient (p + 1) → ℝ), Measurable g →
        ∀ B : ℝ, (∀ x, |g x| ≤ B) → Integrable g volume →
          (∀ x, g x ≠ 0 → x ∈ ball a H) →
          Tendsto (fun j =>
            (∫ x, scalarCappedTransform (p + 1) (volume.restrict (ball a R))
              e ((1 / 2 : ℝ) ^ (s j)) f x * g x) +
            ∫ x, (∫ y in closedExterior a R, f y *
              inner ℝ e (kernel (p + 1) x y - kernel (p + 1) a y)) * g x)
            atTop (𝓝 (b * ∫ x, g x)) := by
  subst ν
  let ρ : Measure (Ambient (p + 1)) := volume.withDensity (fun x => ENNReal.ofReal (f x))
  have hgρ : GlobalUpperGrowth (p + 1) G ρ := by
    refine ⟨hgν.1, ?_⟩
    intro x r hr
    have hpre : L ⁻¹' ball (L x) r = ball x r := by
      ext y
      simp only [mem_preimage, mem_ball, L.dist_map]
    have h := hgν.2 (L x) r hr
    rw [Measure.map_apply L.continuous.measurable measurableSet_ball, hpre] at h
    exact h
  obtain ⟨s, hs, hεlim, v, _, hlim, b, hconstant⟩ :=
    exists_local_constant_transform_of_source_L2 p C G cMass μ (ρ.map L)
      hgrowth hgν hweak D hB (L e) (L a) H R hH hR hHR hboundary hmass hcMass hlowerMass hreflect
  obtain ⟨_, hlimIntrinsic⟩ := local_capped_weak_L2_pairings_linearIsometry (p + 1) L ρ e a R
    (fun j => (1 / 2 : ℝ) ^ (s j)) v (Lp.memLp v) hlim
  have hconstantIntrinsic := local_transform_constancy_linearIsometry (p + 1) L ρ e a H R b v hconstant
  refine ⟨s, hs, hεlim, b, ?_⟩
  intro g hg B hBg hgI hgs
  exact unweighted_capped_pairing_tendsto_constant (p + 1) G f hf c hc hlower hgρ e a H R b
    hH hR hHR (fun j => (1 / 2 : ℝ) ^ (s j)) (fun x => v (L x))
    hlimIntrinsic hconstantIntrinsic g hg B hBg hgI hgs

end

end RieszRectifiability

end OAI
