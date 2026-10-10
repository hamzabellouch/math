import Mathlib
import OAI.Analysis.RieszRectifiability.Rigidity.ReflectionlessAnnularBounds
import OAI.Analysis.RieszRectifiability.Kernel.LocalRenormalizedRepresentative
import OAI.Analysis.RieszRectifiability.Foundations.LocalTestConstancy

namespace OAI

/-!
# Local constancy from reflectionlessness

A renormalized local transform annihilates mean-zero Lipschitz tests under
reflectionlessness. A normalized ball bump and local L² integrability then identify
the transform with a constant almost everywhere on the inner ball.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology Function
open scoped NNReal ENNReal

theorem local_transform_constant_of_reflectionless {d : ℕ} (p : ℕ) (C c : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hg : GlobalUpperGrowth (p + 1) C μ) (hc : 0 < c)
    (e a : Ambient d) (H R : ℝ) (hH : 0 < H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hmass : ENNReal.ofReal (c * (H / 4) ^ (p + 1)) ≤ μ (ball a (H / 4)))
    (v : Lp ℝ 2 (μ.restrict (ball a R)))
    (hv : ∀ (φ : Ambient d → ℝ) (L B : ℝ≥0), LipschitzWith L φ →
      (∀ x, |φ x| ≤ (B : ℝ)) → (∫ x in ball a R, v x * φ x ∂μ) =
        (1 / 2 : ℝ) * (∫ q, rieszInteriorIntegrand (p + 1) e φ q
          ∂(μ.restrict (ball a R)).prod (μ.restrict (ball a R))))
    (hreflect : ScalarReflectionlessAt (p + 1) μ a) :
    ∃ b : ℝ, ∀ᵐ x ∂μ, x ∈ ball a H →
      v x + scalarFarRieszTransform (p + 1) μ e a R x = b := by
  let := finiteMeasure_restrict_ball_of_globalGrowth (p + 1) C μ hg a H hH
  obtain ⟨hL2, hpair⟩ := local_renormalized_pairing_representation p C μ hg e a H R hH hR hHR v hv
  obtain ⟨η, Kη, hηc, hη, _, hηs, hηmean, _⟩ :=
    exists_normalized_ball_bump (p + 1) C c μ hg hc a (H / 4) (by positivity) hmass
  have hηU : support η ⊆ ball a H := by
    intro x hx
    exact (hηs x hx).trans_lt (by linarith : 2 * (H / 4) < H)
  apply local_mean_zero_test_annihilator_constant μ (ball a H) isOpen_ball
    (fun x => v x + scalarFarRieszTransform (p + 1) μ e a R x)
    (hL2.integrable (by norm_num)) η Kη hη hηc hηU hηmean
  intro φ K hφ hφc hφs hφmean
  obtain ⟨B, hB⟩ := hφc.exists_bound_of_continuous hφ.continuous
  have hb : ∀ x, |φ x| ≤ (Real.toNNReal B : ℝ) := by
    intro x
    have hb' : |φ x| ≤ B := by simpa only [Real.norm_eq_abs] using! hB x
    exact hb'.trans (Real.le_coe_toNNReal B)
  have hs : ∀ x, φ x ≠ 0 → dist x a ≤ H := fun x hx => (hφs hx).le
  rw [← hpair φ K (Real.toNNReal B) hφ hb hs]
  exact hreflect e φ K H R hφ hH.le hR hHR hs hφmean

theorem exists_local_constant_transform_of_source_L2 {d : ℕ} (p : ℕ) (C G c : ℝ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hgrowth : ∀ j, GlobalUpperGrowth (p + 1) C (μ j))
    (hgν : GlobalUpperGrowth (p + 1) G ν) (hweak : CompactTestConvergence μ ν)
    (D : ℝ≥0)
    (hB : ∀ j ε, 0 < ε → ∀ f : Ambient d → ℝ, MemLp f 2 (μ j) →
      MemLp (truncated (p + 1) (μ j) ε f) 2 (μ j) ∧
        eLpNorm (truncated (p + 1) (μ j) ε f) 2 (μ j) ≤ (D : ℝ≥0∞) * eLpNorm f 2 (μ j))
    (e a : Ambient d) (H R : ℝ) (hH : 0 < H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hboundary : ν (frontier (ball a R)) = 0) (hmass : ν (ball a R) ≠ 0)
    (hc : 0 < c) (hlower : ENNReal.ofReal (c * (H / 4) ^ (p + 1)) ≤ ν (ball a (H / 4)))
    (hreflect : ScalarReflectionlessAt (p + 1) ν a) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧
      Tendsto (fun j => (1 / 2 : ℝ) ^ (ρ j)) atTop (𝓝 0) ∧
      ∃ v : Lp ℝ 2 (ν.restrict (ball a R)),
        ‖v‖ ≤ (Real.toNNReal (‖e‖ * ((D : ℝ) + C * 2 ^ (p + 1))) : ℝ) *
          Real.sqrt (ν.real (ball a R)) ∧
        (∀ g : Ambient d → ℝ, MemLp g 2 (ν.restrict (ball a R)) →
          Tendsto (fun j => ∫ x in ball a R,
            scalarCappedTransform (p + 1) (ν.restrict (ball a R)) e ((1 / 2 : ℝ) ^ (ρ j))
              (fun _ => 1) x * g x ∂ν) atTop (𝓝 (∫ x in ball a R, v x * g x ∂ν))) ∧
        ∃ b : ℝ, ∀ᵐ x ∂ν, x ∈ ball a H →
          v x + scalarFarRieszTransform (p + 1) ν e a R x = b := by
  obtain ⟨ρ, hρ, hεlim, v, hv, hlim, hrep⟩ := exists_local_L2_interior_representative
    p C G μ ν hgrowth hgν hweak D hB a R hboundary hmass e
  exact ⟨ρ, hρ, hεlim, v, hv, hlim,
    local_transform_constant_of_reflectionless p G c ν hgν hc e a H R hH hR hHR hlower v hrep hreflect⟩

end

end RieszRectifiability

end OAI
