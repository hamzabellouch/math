import OAI.Geometry.CylinderCovering.Caps.FiniteGeometry
import OAI.Geometry.CylinderCovering.Caps.FiniteProperties
import OAI.Geometry.CylinderCovering.Caps.FiniteLimit
import OAI.Geometry.CylinderCovering.Caps.FiniteAsymptotics
import OAI.Geometry.CylinderCovering.Caps.CapRegularity

namespace OAI

open Set Filter
open scoped Topology
noncomputable section
namespace CylinderCovering.HalfheightFinite

theorem family_conclusion_of_covered {δ : ℝ} (hδ : 0 ≤ δ) {R : ℝ → ℝ}
    (hR : ContinuousOn R (Icc (-1:ℝ) 1))
    (hR0 : ∀ r ∈ Icc (-1:ℝ) 1, 0 ≤ R r)
    (hcover : HalfHeightCaps.Covered δ R) : FamilyConclusion δ R := by
  refine ⟨?_, totalArea_tendsto hδ hR hR0⟩
  intro N hN
  refine ⟨?_, finite_coverage hδ hR hcover hN⟩
  intro i
  exact ⟨firstBase_properties δ R N i, secondBase_properties δ R N i,
    firstBase_area hδ hR hR0 N i, secondBase_area hδ hR hR0 N i⟩

theorem cubic_family {δ : ℝ} (hδ : 0 < δ) :
    FamilyConclusion δ (cubicCap δ) := by
  apply family_conclusion_of_covered hδ.le (cubicCap_continuous δ).continuousOn
    (fun r _ => (cubicCap_positive hδ.le r).le)
  exact HalfHeightCaps.cubic_covers hδ

theorem fractional_family {δ : ℝ} (hδ : 0 < δ) (hsmall : δ ≤ 1) :
    FamilyConclusion δ (fractionalCap δ) := by
  apply family_conclusion_of_covered hδ.le (fractionalCap_continuous δ).continuousOn
    (fun r _ => (fractionalCap_positive hδ.le r).le)
  exact HalfHeightCaps.fractional_covers hδ hsmall

theorem eventually_cubic_family :
    ∀ᶠ δ : ℝ in 𝓝[>] 0, FamilyConclusion δ (cubicCap δ) := by
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact cubic_family hδ

theorem eventually_fractional_family :
    ∀ᶠ δ : ℝ in 𝓝[>] 0, FamilyConclusion δ (fractionalCap δ) := by
  have hs : ∀ᶠ δ : ℝ in 𝓝[>] 0, δ < 1 :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (gt_mem_nhds (by norm_num : (0:ℝ) < 1))
  filter_upwards [self_mem_nhdsWithin, hs] with δ hδ hsmall
  exact fractional_family hδ hsmall.le

theorem full_halfheight : Statement := by
  exact ⟨fun δ hδ _ => cubic_family hδ, eventually_fractional_family,
    cubic_cost_bigO, fractional_cost_bigO,
    eventual_finite_saving eventually_cubic_family eventually_fractional_family⟩

end CylinderCovering.HalfheightFinite

end

end OAI
