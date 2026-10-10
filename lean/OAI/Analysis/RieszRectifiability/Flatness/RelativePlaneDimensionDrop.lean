import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.SubspaceTangentSupport
import OAI.Analysis.RieszRectifiability.Flatness.NonflatAnnularHyperplaneTangent

namespace OAI

/-!
# Dimension drop inside a supporting plane

A hole in the support within a linear subspace gives a halfspace tangent and then a
hyperplane tangent. Their support lies in a strictly smaller subspace while retaining
growth, lower mass, annular bounds, and quantitative bilateral nonflatness.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

theorem exists_relative_plane_dimension_drop {n d : ℕ} (hn : 1 ≤ n) (hnd : n ≤ d)
    (μ : Measure (Ambient d)) (hne : μ ≠ 0) (C G B ε : ℝ) (hC : 0 < C)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ R : ℝ, 0 < R →
      ENNReal.ofReal (R ^ n / C) ≤ μ (ball x R))
    (hB : GlobalSmoothAnnularBound n μ B) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hbad : GlobalBilateralLower n μ ε)
    (P : Submodule ℝ (Ambient d)) (hP : μ.support ⊆ (P : Set (Ambient d)))
    (c : Ambient d) (hcP : c ∈ P) (hc : c ∉ μ.support) :
    ∃ Q : Submodule ℝ (Ambient d), Module.finrank ℝ Q < Module.finrank ℝ P ∧
      ∃ ν : Measure (Ambient d), IsFiniteMeasureOnCompacts ν ∧ ν ≠ 0 ∧
        GlobalUpperGrowth n ((G * 2 ^ n) * 2 ^ n) ν ∧ (0 : Ambient d) ∈ ν.support ∧
        (∀ x ∈ ν.support, ∀ R : ℝ, 0 < R →
          ENNReal.ofReal (R ^ n / ((C * 4 ^ n) * 4 ^ n)) ≤ ν (ball x R)) ∧
        ν.support ⊆ (Q : Set (Ambient d)) ∧ GlobalSmoothAnnularBound n ν B ∧
        GlobalBilateralLower n ν (ε / 4096) := by
  let r := fun j : ℕ => (1 / 2 : ℝ) ^ j
  have hr (j : ℕ) : 0 < r j := by dsimp only [r]; positivity
  have hr0 : Tendsto r atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨a, ha, hac, ρ, hρ, η, hfiniteη, hneη, hlocalη, hgη, hzeroη, hlowerη, hsideη⟩ :=
    exists_nonzero_halfspace_tangent_of_hole n μ hne C G hC hg hlower c hc r hr hr0
  let := hfiniteη
  have hηP := blowup_limit_support_submodule n μ η G hg P hP a (hP ha)
    (fun j => r (ρ j)) (fun j => hr (ρ j)) hlocalη
  have hBη : GlobalSmoothAnnularBound n η B := by
    apply GlobalSmoothAnnularBound.compact_limit n G B
      (fun j => blowupMeasure n μ a (r (ρ j))) η
      (fun j => blowupMeasure_growth n μ a (r (ρ j)) G (hr (ρ j)) hg) hlocalη
    exact Eventually.of_forall fun j => GlobalSmoothAnnularBound.blowup n μ B hB a (r (ρ j)) (hr (ρ j))
  have hbadη := GlobalBilateralLower.tangent hn hnd μ η C G hC hg hlower a ha
    (fun j => r (ρ j)) (fun j => hr (ρ j)) hlocalη ε hε hε1 hbad
  have he : a - c ≠ 0 := sub_ne_zero.mpr hac
  have heP : a - c ∈ P := P.sub_mem (hP ha) hcP
  have hεη : 0 < ε / 64 := by positivity
  have hεη1 : ε / 64 ≤ 1 := by linarith
  obtain ⟨σ, _, ν, hfiniteν, hneν, hlocalν, hgν, hzeroν, hlowerν, hplaneν, _, hBν, hbadν⟩ :=
    exists_nonflat_annular_hyperplane_tangent hn hnd η (C * 4 ^ n) (G * 2 ^ n) B (ε / 64)
      (by positivity) hgη hlowerη hzeroη hBη hεη hεη1 hbadη (a - c) he hsideη r hr hr0
  let := hfiniteν
  have hνP := blowup_limit_support_submodule n η ν (G * 2 ^ n) hgη P hηP 0 P.zero_mem
    (fun j => r (σ j)) (fun j => hr (σ j)) hlocalν
  refine ⟨P ⊓ (innerSL ℝ (a - c)).toLinearMap.ker, normal_section_finrank_lt P (a - c) heP he,
    ν, hfiniteν, hneν, hgν, hzeroν, hlowerν, ?_, hBν, ?_⟩
  · intro x hx
    exact ⟨hνP hx, hplaneν x hx⟩
  · convert! hbadν using 1
    ring

end

end RieszRectifiability

end OAI
