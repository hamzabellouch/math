import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.ShrinkingSmoothCutoffs
import OAI.Analysis.RieszRectifiability.Rigidity.ShrinkingJetSeminorms

namespace OAI

namespace RieszRectifiability

noncomputable section

open SchwartzMap Metric Set Filter Topology
open scoped ContDiff

def shrinkingRadius (j : ℕ) : ℝ := ((j : ℝ) + 2)⁻¹

theorem shrinkingRadius_pos (j : ℕ) : 0 < shrinkingRadius j := by
  unfold shrinkingRadius
  positivity

theorem shrinkingRadius_small (j : ℕ) : 2 * shrinkingRadius j ≤ 1 := by
  unfold shrinkingRadius
  apply (mul_inv_le_iff₀ (by positivity : (0 : ℝ) < (j : ℝ) + 2)).2
  linarith [Nat.cast_nonneg (α := ℝ) j]

theorem shrinkingRadius_tendsto : Tendsto shrinkingRadius atTop (𝓝 0) := by
  have ht : Tendsto (fun j : ℕ => (j : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  exact ht.inv_tendsto_atTop

theorem shrinking_cutoff_temperate (d j : ℕ) :
    (scaledSmoothCutoff d (shrinkingRadius j)).HasTemperateGrowth :=
  (scaledSmoothCutoff_compact d _ (shrinkingRadius_pos j)).hasTemperateGrowth
    (scaledSmoothCutoff_smooth d _)

def shrinkingSchwartzCutoff {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : 𝓢(Ambient d, F)) (j : ℕ) : 𝓢(Ambient d, F) :=
  smulLeftCLM F (scaledSmoothCutoff d (shrinkingRadius j)) g

theorem shrinkingSchwartzCutoff_apply {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : 𝓢(Ambient d, F)) (j : ℕ) (x : Ambient d) :
    shrinkingSchwartzCutoff g j x = scaledSmoothCutoff d (shrinkingRadius j) x • g x :=
  smulLeftCLM_apply_apply (shrinking_cutoff_temperate d j) g x

theorem shrinkingSchwartzCutoff_germ {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : 𝓢(Ambient d, F)) (j : ℕ) :
    (shrinkingSchwartzCutoff g j : Ambient d → F) =ᶠ[𝓝 (0 : Ambient d)] g := by
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (shrinkingRadius_pos j))] with x hx
  rw [shrinkingSchwartzCutoff_apply,
    scaledSmoothCutoff_one d _ (shrinkingRadius_pos j) x hx, one_smul]

theorem shrinkingSchwartzCutoff_seminorm_tendsto {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : 𝓢(Ambient d, F)) (k n : ℕ)
    (hz : ∀ i, i ≤ n → iteratedFDeriv ℝ i g 0 = 0) :
    Tendsto (fun j => SchwartzMap.seminorm ℝ k n (shrinkingSchwartzCutoff g j))
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hb⟩ := scaledSmoothCutoff_derivatives d
  have hlim : Tendsto (fun j => SchwartzMap.seminorm ℝ 0 (n + 1) g *
      jetCutoffCoefficient C n * shrinkingRadius j) atTop (𝓝 0) := by
    simpa only [mul_zero] using! tendsto_const_nhds.mul shrinkingRadius_tendsto
  apply squeeze_zero (fun j => apply_nonneg _ _) _ hlim
  intro j
  exact zero_jet_localized_seminorm_bound g k n hz _ (shrinking_cutoff_temperate d j)
    C hC (shrinkingRadius j) (shrinkingRadius_pos j) (shrinkingRadius_small j)
    (hb _ (shrinkingRadius_pos j)) (scaledSmoothCutoff_support d _ (shrinkingRadius_pos j))

end

end RieszRectifiability

end OAI
