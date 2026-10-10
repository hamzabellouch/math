import OAI.Analysis.CircleDomains.Selection.RegularLevelFlowOrbit
import OAI.Analysis.CircleDomains.Selection.RegularContours
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

namespace OAI

/-! A nonstationary trajectory has nonzero speed in the actual local
one-dimensional coordinate of its regular level. -/
open Set Function Filter
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma level_flow_coordinate_deriv_ne_zero {f : ℂ → ℝ} {a : ℝ}
    (F : CompactRegularLevelFlow f a) (x : {z // f z = a}) (t : ℝ)
    (e : OpenPartialHomeomorph ℂ (ℝ × ℝ))
    (ht : F.trajectory x t ∈ e.source) (he : ∀ z, (e z).1 = f z)
    (hs : ContDiff ℝ ∞ e) (hi : ContDiffOn ℝ ∞ e.symm e.target) :
    deriv (fun s => (e (F.trajectory x s)).2) t ≠ 0 := by
  let γ := F.trajectory x
  have hg : ContDiff ℝ ∞ (fun s => (e (γ s)).2) := (hs.comp (F.trajectory_smooth x)).snd
  have hfirst : (fun s => (e (γ s)).1) = (fun _ => a) := by
    funext s
    exact (he (γ s)).trans (F.scalar x s)
  have h1 : HasDerivAt (fun s => (e (γ s)).1) 0 t := by
    rw [hfirst]
    exact hasDerivAt_const t a
  intro hzero
  have h2 : HasDerivAt (fun s => (e (γ s)).2) 0 t := by
    rw [← hzero]
    exact (hg.differentiable (by simp) t).hasDerivAt
  have heγ : HasDerivAt (fun s => e (γ s)) (0 : ℝ × ℝ) t := h1.prodMk h2
  have hei := (hi.contDiffAt (e.open_target.mem_nhds (e.map_source ht))).differentiableAt (by simp)
  have hd := hei.hasFDerivAt.comp_hasDerivAt t heγ
  have hfun : (e.symm ∘ fun s => e (γ s)) =ᶠ[𝓝 t] γ := by
    filter_upwards [((F.trajectory_smooth x).continuous.continuousAt).preimage_mem_nhds
      (e.open_source.mem_nhds ht)] with s hs
    exact e.left_inv hs
  have hz : HasDerivAt γ 0 t := by
    simpa only [map_zero] using hd.congr_of_eventuallyEq hfun.symm
  exact F.regular x t hz.deriv

lemma level_flow_coordinate_open_image {f : ℂ → ℝ} {a : ℝ}
    (F : CompactRegularLevelFlow f a) (x : {z // f z = a}) (t : ℝ)
    (e : OpenPartialHomeomorph ℂ (ℝ × ℝ))
    (ht : F.trajectory x t ∈ e.source) (he : ∀ z, (e z).1 = f z)
    (hs : ContDiff ℝ ∞ e) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    {U : Set ℝ} (hU : U ∈ 𝓝 t) :
    (fun s => (e (F.trajectory x s)).2) '' U ∈ 𝓝 ((e (F.trajectory x t)).2) := by
  have hg : ContDiff ℝ ∞ (fun s => (e (F.trajectory x s)).2) :=
    (hs.comp (F.trajectory_smooth x)).snd
  have hd := (hg.contDiffAt (x := t)).hasStrictDerivAt (by simp)
  rw [← hd.map_nhds_eq (level_flow_coordinate_deriv_ne_zero F x t e ht he hs hi)]
  exact Filter.mem_map_iff_exists_image.mpr ⟨U,hU,subset_refl _⟩

end CircleDomainRigidity

end

end OAI
