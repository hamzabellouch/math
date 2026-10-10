import OAI.Geometry.SurfaceImmersion.Whitney.SmoothCompactArc
import Mathlib.Analysis.Calculus.Deriv.Slope

namespace OAI

/-! The orientation required for joining is forced by separation of the
old and new compact arc interiors. It is not an additional geometric choice. -/
noncomputable section
open Set Filter
open scoped Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {N : Type*}

theorem arc_join_deriv_pos {γ δ : ℝ → N} {h : ℝ → ℝ} {l a c d : ℝ}
    (hla : l < a) (hcd : c < d) (hh : DifferentiableAt ℝ h a)
    (hne : deriv h a ≠ 0) (ha : h a = c)
    (he : γ =ᶠ[𝓝 a] δ ∘ h)
    (hcross : ∀ s ∈ Icc l a, ∀ t ∈ Ioc c d, γ s ≠ δ t) :
    0 < deriv h a := by
  have hsmall : ∀ᶠ t in 𝓝 a, l < t ∧ h t < d :=
    (eventually_gt_nhds hla).and (hh.continuousAt.eventually (gt_mem_nhds (ha ▸ hcd)))
  have hslope : ∀ᶠ t in 𝓝[<] a, 0 ≤ slope h a t := by
    filter_upwards [hsmall.filter_mono nhdsWithin_le_nhds,
      he.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with t ht heq hta
    have hc : h t ≤ c := by
      by_contra hc
      exact hcross t ⟨ht.1.le,hta.le⟩ (h t) ⟨lt_of_not_ge hc,ht.2.le⟩ heq
    rw [slope_def_field]
    exact div_nonneg_of_nonpos (sub_nonpos.mpr (ha ▸ hc)) (sub_nonpos.mpr hta.le)
  have hlim := (hasDerivAt_iff_tendsto_slope_left_right.mp hh.hasDerivAt).1
  exact lt_of_le_of_ne (ge_of_tendsto hlim hslope) hne.symm

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
