import OAI.Analysis.KadisonKastler.BaireMeasurableBranch
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! # A Borel section for an almost-everywhere surjective Baire parametrization

Measurable hulls choose a coherent sequence of prefixes. Continuity identifies
the resulting branch with the point whose hulls were followed.
-/

namespace KadisonKastler

open MeasureTheory Set Filter
open scoped Topology

noncomputable section

variable {X : Type*} [MeasurableSpace X] [MetricSpace X] [BorelSpace X]

omit [BorelSpace X] in
theorem baireChosenBranch_rightInverse (μ : Measure X) (F : (ℕ → ℕ) → X)
    (hF : Continuous F) (x : X) (hx : x ∈ baireImageHull μ F [])
    (hchildren : ∀ s : List ℕ, x ∈ baireImageHull μ F s →
      ∃ n, x ∈ baireImageHull μ F (n :: s)) :
    F (baireChosenBranch μ F x) = x := by
  let b := baireChosenBranch μ F x
  have hcl (n : ℕ) : x ∈ closure (F '' PiNat.cylinder b n) := by
    have hh := (baireChosenBranch_hull μ F x hx hchildren n).2
    have hb : b ∈ bairePrefixCylinder (baireChosenWord μ F n x) := by
      change PiNat.res b (baireChosenWord μ F n x).length = baireChosenWord μ F n x
      rw [baireChosenWord_length]
      exact baireChosenBranch_res μ F x n
    rwa [bairePrefixCylinder_eq _ hb, baireChosenWord_length] at hh
  have happ (n : ℕ) : ∃ a ∈ PiNat.cylinder b n, dist (F a) x < 1 / (n + 1 : ℝ) := by
    obtain ⟨y, ⟨a, ha, rfl⟩, hy⟩ := (Metric.mem_closure_iff.mp (hcl n))
      (1 / (n + 1 : ℝ)) (by positivity)
    exact ⟨a, ha, by simpa only [dist_comm] using hy⟩
  choose a ha hdist using happ
  have halim : Tendsto a atTop (𝓝 b) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (i + 1)] with n hn
    exact (PiNat.mem_cylinder_iff.mp (ha n) i (by omega)).symm
  have hFlim : Tendsto (fun n => F (a n)) atTop (𝓝 x) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall (fun _ => dist_nonneg))
      (Eventually.of_forall (fun n => (hdist n).le))
      tendsto_one_div_add_atTop_nhds_zero_nat
  exact tendsto_nhds_unique (hF.tendsto b |>.comp halim) hFlim

theorem exists_measurable_baire_section (μ : Measure X) [IsFiniteMeasure μ]
    (F : (ℕ → ℕ) → X) (hF : Continuous F)
    (hsurj : ∀ᵐ x ∂μ, ∃ a, F a = x) :
    ∃ g : X → (ℕ → ℕ), Measurable g ∧ ∀ᵐ x ∂μ, F (g x) = x := by
  refine ⟨baireChosenBranch μ F, measurable_baireChosenBranch μ F, ?_⟩
  filter_upwards [hsurj, baireImageHull_all_children_ae μ F] with x hx hc
  apply baireChosenBranch_rightInverse μ F hF x ?_ hc
  apply image_subset_baireImageHull μ F []
  obtain ⟨a, rfl⟩ := hx
  exact ⟨a, by simp, rfl⟩

end

end KadisonKastler

end OAI
