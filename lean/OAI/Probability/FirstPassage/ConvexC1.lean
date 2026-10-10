import OAI.Probability.FirstPassage.GlobalDifferentiability
import Mathlib.Analysis.Calculus.Darboux
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations

namespace OAI

namespace PlanarFPP
open Set Filter
open scoped Topology

lemma convex_continuous_deriv (φ : ℝ → ℝ) (hc : ConvexOn ℝ univ φ)
    (hd : Differentiable ℝ φ) : Continuous (deriv φ) := by
  let g := fun x => deriv φ x+x
  have hm : Monotone g := fun x y h => add_le_add
    (hc.monotoneOn_deriv (fun x _ => hd x) (mem_univ x) (mem_univ y) h) h
  have hg (x : ℝ) : HasDerivAt (fun t => φ t+t^2/2) (g x) x := by
    have hq : HasDerivAt (fun t : ℝ => t^2/2) x x := by
      simpa using ((hasDerivAt_id x).pow 2).div_const 2
    exact (hd x).hasDerivAt.add hq
  have hsurj : Function.Surjective g := by
    intro y
    let a := min 0 (y-deriv φ 0-1)
    let b := max 0 (y-deriv φ 0+1)
    have ha : a ≤ 0 := min_le_left ..
    have hb : 0 ≤ b := le_max_left ..
    have hda := hc.monotoneOn_deriv (fun x _ => hd x) (mem_univ a) (mem_univ 0) ha
    have hdb := hc.monotoneOn_deriv (fun x _ => hd x) (mem_univ 0) (mem_univ b) hb
    have hay : a ≤ y-deriv φ 0-1 := min_le_right ..
    have hby : y-deriv φ 0+1 ≤ b := le_max_right ..
    have hga : g a < y := by dsimp [g]; linarith
    have hgb : y < g b := by dsimp [g]; linarith
    obtain ⟨x,_hx,hx⟩ := exists_hasDerivWithinAt_eq_of_gt_of_lt (ha.trans hb)
      (fun x _ => (hg x).hasDerivWithinAt) hga hgb
    exact ⟨x,hx⟩
  have hcont := hm.continuous_of_surjective hsurj
  convert hcont.sub continuous_id using 1
  funext x
  dsimp [g]
  ring

lemma convex_contDiff_one (φ : ℝ → ℝ) (hc : ConvexOn ℝ univ φ)
    (hd : Differentiable ℝ φ) : ContDiff ℝ 1 φ :=
  contDiff_one_iff_deriv.mpr ⟨hd,convex_continuous_deriv φ hc hd⟩

end PlanarFPP

end OAI
