import Mathlib.Topology.UniformSpace.Path
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

/-! Dyadic subdivision with quantitative oscillation and pointwise error
preservation when two replacement paths are concatenated. -/
open Set Function Filter Metric unitInterval
open scoped Topology unitInterval
noncomputable section
namespace CircleDomainRigidity

def leftHalf (t : I) : I := ⟨(t : ℝ) / 2, by constructor <;> linarith [t.property.1, t.property.2]⟩
def rightHalf (t : I) : I := ⟨((t : ℝ) + 1) / 2, by constructor <;> linarith [t.property.1, t.property.2]⟩

lemma dist_leftHalf (s t : I) : dist (leftHalf s) (leftHalf t) = (1 / 2 : ℝ) * dist s t := by
  change |(s : ℝ) / 2 - (t : ℝ) / 2| = (1 / 2 : ℝ) * |(s : ℝ) - (t : ℝ)|
  rw [← sub_div, abs_div]
  norm_num
  ring

lemma dist_rightHalf (s t : I) : dist (rightHalf s) (rightHalf t) = (1 / 2 : ℝ) * dist s t := by
  change |((s : ℝ) + 1) / 2 - ((t : ℝ) + 1) / 2| = (1 / 2 : ℝ) * |(s : ℝ) - (t : ℝ)|
  rw [show ((s : ℝ) + 1) / 2 - ((t : ℝ) + 1) / 2 = ((s : ℝ) - t) / 2 by ring, abs_div]
  norm_num
  ring

def dyadicSmallOscillation {E : Type*} [PseudoMetricSpace E] : ℕ → (I → E) → ℝ → Prop
  | 0, f, ε => ∀ s t, dist (f s) (f t) < ε
  | n + 1, f, ε => dyadicSmallOscillation n (f ∘ leftHalf) ε ∧
      dyadicSmallOscillation n (f ∘ rightHalf) ε

lemma dyadicSmallOscillation_of_modulus {E : Type*} [PseudoMetricSpace E]
    (n : ℕ) (f : I → E) (ε : ℝ)
    (hf : ∀ s t, dist s t ≤ (1 / 2 : ℝ)^n → dist (f s) (f t) < ε) :
    dyadicSmallOscillation n f ε := by
  induction n generalizing f with
  | zero =>
      intro s t
      apply hf
      simp only [pow_zero]
      change |(s : ℝ) - (t : ℝ)| ≤ 1
      exact abs_le.mpr ⟨by linarith [s.property.1, t.property.2], by linarith [s.property.2, t.property.1]⟩
  | succ n ih =>
      constructor
      · apply ih
        intro s t hst
        apply hf
        rw [dist_leftHalf, pow_succ']
        exact mul_le_mul_of_nonneg_left hst (by norm_num : (0 : ℝ) ≤ 1 / 2)
      · apply ih
        intro s t hst
        apply hf
        rw [dist_rightHalf, pow_succ']
        exact mul_le_mul_of_nonneg_left hst (by norm_num : (0 : ℝ) ≤ 1 / 2)

lemma exists_dyadicSmallOscillation {E : Type*} [PseudoMetricSpace E]
    {f : I → E} (hf : Continuous f) {ε : ℝ} (hε : 0 < ε) :
    ∃ n, dyadicSmallOscillation n f ε := by
  have hu := CompactSpace.uniformContinuous_of_continuous hf
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuous_iff.mp hu ε hε
  have ht : Tendsto (fun n : ℕ => (1 / 2 : ℝ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds hδ)).exists
  exact ⟨n, dyadicSmallOscillation_of_modulus n f ε (fun s t hst => hmod (hst.trans_lt hn))⟩

lemma path_trans_pointwise_error {E : Type*} [MetricSpace E] {a b c : E}
    (γ₀ : Path a b) (γ₁ : Path b c) (f : I → E) {ε : ℝ}
    (h₀ : ∀ t, dist (γ₀ t) (f (leftHalf t)) < ε)
    (h₁ : ∀ t, dist (γ₁ t) (f (rightHalf t)) < ε) :
    ∀ t, dist ((γ₀.trans γ₁) t) (f t) < ε := by
  intro t
  rw [Path.trans_apply]
  split_ifs with ht
  · let s : I := ⟨2 * t, (mul_pos_mem_iff zero_lt_two).2 ⟨t.property.1, ht⟩⟩
    have hs : leftHalf s = t := by apply Subtype.ext; dsimp [leftHalf, s]; ring
    simpa only [hs] using h₀ s
  · let s : I := ⟨2 * t - 1, two_mul_sub_one_mem_iff.2 ⟨(not_le.mp ht).le, t.property.2⟩⟩
    have hs : rightHalf s = t := by apply Subtype.ext; dsimp [rightHalf, s]; ring
    simpa only [hs] using h₁ s

end CircleDomainRigidity

end

end OAI
