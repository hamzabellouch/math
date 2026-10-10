import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.GrowthVolumeDomination

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem intrinsic_growth_not_supported_in_hyperplane (n : ℕ)
    (μ : Measure (Ambient n)) (G : ℝ) (hg : GlobalUpperGrowth n G μ) (hμ : μ ≠ 0)
    (e : Ambient n) (he : e ≠ 0) :
    ¬ (∀ x ∈ μ.support, inner ℝ e x = 0) := by
  intro hside
  let S : Submodule ℝ (Ambient n) := (innerSL ℝ e).ker
  have hproper : S ≠ ⊤ := by
    intro htop
    have hemem : e ∈ S := by rw [htop]; trivial
    have hinner : inner ℝ e e = 0 := hemem
    exact he (inner_self_eq_zero.mp hinner)
  have hvol : (volume : Measure (Ambient n)) (S : Set (Ambient n)) = 0 :=
    Measure.addHaar_submodule volume S hproper
  have hnull : μ (S : Set (Ambient n)) = 0 :=
    intrinsic_growth_absolutelyContinuous n G μ hg hvol
  have hsnull : μ μ.support = 0 := measure_mono_null (fun x hx => hside x hx) hnull
  have huniv : μ univ = 0 := by
    apply le_antisymm _ bot_le
    calc
      μ univ = μ (μ.support ∪ μ.supportᶜ) := by rw [union_compl_self]
      _ ≤ μ μ.support + μ μ.supportᶜ := measure_union_le _ _
      _ = 0 := by rw [hsnull, μ.measure_compl_support, zero_add]
  exact hμ (Measure.measure_univ_eq_zero.mp huniv)

end

end RieszRectifiability

end OAI
