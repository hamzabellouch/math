import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.ChartTensorCoordLocal1

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff
namespace YauCounterexamples
namespace ContinuousSmoothFamilyOn
variable {P Q E F G : Type*} [TopologicalSpace P] [TopologicalSpace Q]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
variable {f : P → E → F} {U V : Set E}
lemma paramComp (hf : ContinuousSmoothFamilyOn f U) (a : Q → P) (ha : Continuous a) :
    ContinuousSmoothFamilyOn (fun q => f (a q)) U := by
  refine ⟨fun q => hf.smooth (a q),fun n => ?_⟩
  exact (hf.jets n).comp ((ha.comp continuous_fst).prodMk continuous_snd).continuousOn
    (fun z hz => ⟨mem_univ _,hz.2⟩)

lemma precomp {f : P → F → G} {U : Set F} {V : Set E}
    (hf : ContinuousSmoothFamilyOn f U) (g : E → F)
    (hg : ∀ x ∈ V, ContDiffAt ℝ ∞ g x) (hmap : MapsTo g V U) :
    ContinuousSmoothFamilyOn (fun p => f p ∘ g) V := by
  refine ⟨fun p x hx => (hf.smooth p (g x) (hmap hx)).comp x (hg x hx),fun n z hz => ?_⟩
  have hgc : ContinuousOn g V := fun x hx => (hg x hx).continuousAt.continuousWithinAt
  have hcg : ContinuousOn (fun z : P × E => (z.1,g z.2)) (univ ×ˢ V) :=
    continuousOn_fst.prodMk (hgc.comp
      continuousOn_snd (fun z hz => hz.2))
  have hq (j : ℕ) : ContinuousWithinAt
      (fun z : P × E => iteratedFDeriv ℝ j (f z.1) (g z.2)) (univ ×ˢ V) z :=
    ((hf.jets j).comp hcg (fun z hz => ⟨mem_univ _,hmap hz.2⟩)) z hz
  have hd (j : ℕ) : ContinuousWithinAt
      (fun z : P × E => iteratedFDeriv ℝ j g z.2) (univ ×ˢ V) z :=
    ((hg z.2 hz.2).continuousAt_iteratedFDeriv
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl j)).comp_continuousWithinAt continuous_snd.continuousWithinAt
  have hc : ContinuousWithinAt (fun z : P × E =>
      (ftaylorSeries ℝ (f z.1) (g z.2)).taylorComp (ftaylorSeries ℝ g z.2) n) (univ ×ˢ V) z := by
    apply tendsto_finsetSum
    intro c _
    change ContinuousWithinAt (fun z : P × E =>
      (c.compAlongOrderedFinpartitionL ℝ E F G (iteratedFDeriv ℝ c.length (f z.1) (g z.2)))
        (fun j => iteratedFDeriv ℝ (c.partSize j) g z.2)) _ z
    exact ((c.compAlongOrderedFinpartitionL ℝ E F G).continuous.continuousAt.comp_continuousWithinAt
      (hq c.length)).eval (continuousWithinAt_pi.mpr (fun j => hd (c.partSize j)))
  apply hc.congr_of_eventuallyEq _ ?_
  · filter_upwards [self_mem_nhdsWithin] with w hw
    exact iteratedFDeriv_comp (hf.smooth w.1 (g w.2) (hmap hw.2)) (hg w.2 hw.2)
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)
  · exact iteratedFDeriv_comp (hf.smooth z.1 (g z.2) (hmap hz.2)) (hg z.2 hz.2)
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)
end ContinuousSmoothFamilyOn
end YauCounterexamples
end

end OAI
