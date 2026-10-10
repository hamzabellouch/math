import Mathlib

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
open scoped NNReal

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology
open MeasureTheory
open scoped ContDiff ENNReal

open Set Filter Manifold Bundle ContinuousLinearMap MeasureTheory
open scoped Topology ContDiff Manifold Bundle ENNReal

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology Manifold

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Bundle
open scoped Topology Bundle

open scoped Topology
open Function Manifold Set
open Manifold Bundle
open scoped Manifold Bundle
open Set

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma linear_of_radial_derivative {f : ℝ → E} {l r a : ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioo l r)) (ha : a ∈ Ioo l r)
    (he : ∀ s ∈ Ioo l r, (s-a) • deriv f s = f s) :
    ∀ s ∈ Ioo l r, f s = (s-a) • deriv f a := by
  have hfd : ∀ s ∈ Ioo l r, ContDiffAt ℝ ∞ f s :=
    fun s hs => hf.contDiffAt (isOpen_Ioo.mem_nhds hs)
  have hdd : ∀ s ∈ Ioo l r, ContDiffAt ℝ ∞ (deriv f) s :=
    fun s hs => (hfd s hs).derivWithin (m := ∞) (by simp)
  have hddd : ∀ s ∈ Ioo l r, ContDiffAt ℝ ∞ (deriv (deriv f)) s :=
    fun s hs => (hdd s hs).derivWithin (m := ∞) (by simp)
  have hdz : ∀ s ∈ Ioo l r, s ≠ a → deriv (deriv f) s = 0 := by
    intro s hs hsa
    have hL := ((hasDerivAt_id s).sub_const a).smul
      ((hdd s hs).differentiableAt (by simp)).hasDerivAt
    have heq : (fun u => (u-a) • deriv f u) =ᶠ[𝓝 s] f := by
      filter_upwards [isOpen_Ioo.mem_nhds hs] with u hu
      exact he u hu
    have H := (hL.congr_of_eventuallyEq heq.symm).unique
      ((hfd s hs).differentiableAt (by simp)).hasDerivAt
    simp only [one_smul,id_eq] at H
    have hz : (s-a) • deriv (deriv f) s = 0 := by
      have H' : deriv f s + (s-a) • deriv (deriv f) s = deriv f s := by
        simpa only [add_comm] using H
      exact add_eq_left.mp H'
    exact (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hsa)
  have hdza : deriv (deriv f) a = 0 := by
    have hnear : deriv (deriv f) =ᶠ[𝓝[≠] a] (fun _ => 0) := by
      filter_upwards [self_mem_nhdsWithin,
        Filter.Eventually.filter_mono nhdsWithin_le_nhds (isOpen_Ioo.mem_nhds ha)] with s hsa hs
      exact hdz s hs hsa
    exact tendsto_nhds_unique ((hddd a ha).continuousAt.mono_left nhdsWithin_le_nhds)
      (tendsto_const_nhds.congr' hnear.symm)
  have hdzall : ∀ s ∈ Ioo l r, deriv (deriv f) s = 0 := by
    intro s hs
    by_cases hsa : s = a
    · simpa only [hsa] using hdza
    · exact hdz s hs hsa
  have hconstant : ∀ s ∈ Ioo l r, deriv f s = deriv f a := by
    intro s hs
    exact isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo l r).isPreconnected
      (fun u hu => ((hdd u hu).differentiableAt (by simp)).differentiableWithinAt) hdzall hs ha
  intro s hs
  calc
    f s = (s-a) • deriv f s := (he s hs).symm
    _ = _ := by rw [hconstant s hs]
end WeakMTWTransport

end

end OAI
