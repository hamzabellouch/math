import Mathlib
import OAI.Analysis.RieszRectifiability.Flatness.FullPlaneLowerDimension
import OAI.Analysis.RieszRectifiability.Kernel.NonconcentrationPoint

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Module
open scoped ENNReal

theorem support_submodule_finrank_ge {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, 0 < r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (hzero : (0 : Ambient d) ∈ μ.support)
    (P : Submodule ℝ (Ambient d)) (hP : μ.support ⊆ (P : Set (Ambient d))) :
    n ≤ Module.finrank ℝ P := by
  by_contra hnot
  have hkn : Module.finrank ℝ P < n := lt_of_not_ge hnot
  have hfinite : μ (ball (0 : Ambient d) 1) ≠ ∞ :=
    ((hg.2 0 1 zero_lt_one).trans_lt ENNReal.ofReal_lt_top).ne
  have hmass := ENNReal.toReal_mono hfinite (hlower 0 hzero 1 zero_lt_one)
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ (1 : ℝ) ^ n / C)] at hmass
  have hm : (1 / C) * (1 : ℝ) ^ n ≤ μ.real (ball (0 : Ambient d) 1) := by
    simpa only [one_pow, mul_one] using! hmass
  obtain ⟨τ, hτ, _, hescape⟩ := exists_uniform_affine_escape_width μ G (1 / C) hg
    (by positivity) 1 zero_lt_one hm
  have hS : IsAffineNPlane (Module.finrank ℝ P) P.toAffineSubspace := by
    refine ⟨⟨0, P.zero_mem⟩, ?_⟩
    rw [Submodule.toAffineSubspace_direction]
  obtain ⟨x, _, hxs, hxaway⟩ := hescape _ hkn P.toAffineSubspace hS
  have hxP : x ∈ (P.toAffineSubspace : Set (Ambient d)) := hP hxs
  rw [infDist_zero_of_mem hxP, mul_one] at hxaway
  exact (not_le_of_gt hτ) hxaway

theorem full_support_submodule_finrank_eq {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, 0 < r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (P : Submodule ℝ (Ambient d)) (hP : μ.support = (P : Set (Ambient d))) :
    Module.finrank ℝ P = n := by
  apply Nat.le_antisymm (full_support_submodule_finrank_le μ C G hC hg hlower P hP)
  apply support_submodule_finrank_ge μ C G hC hg hlower _ P hP.subset
  rw [hP]
  exact P.zero_mem

end

end RieszRectifiability

end OAI
