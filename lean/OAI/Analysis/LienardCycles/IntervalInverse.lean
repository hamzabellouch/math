import OAI.Analysis.LienardCycles.SharpPhysical

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open scoped Topology
open Set Filter Metric
open scoped Topology ContDiff
open scoped Topology NNReal
open Set Filter
open scoped Topology ContDiff NNReal

open Set Filter
open scoped Topology
namespace QuinticLienard.RealAnalysis

theorem continuous_interval_inverse {f : ℝ → ℝ} {a b c d : ℝ} (hcd : c≤d)
    (hc : ContinuousOn f (Icc a b)) (hb : BijOn f (Icc a b) (Icc c d)) :
    ∃ g : ℝ → ℝ, Continuous g ∧ (∀ y,g y ∈ Icc a b) ∧
      (∀ y ∈ Icc c d,f (g y)=y) ∧ (∀ t ∈ Icc a b,g (f t)=t) := by
  let F : Icc a b → Icc c d := fun t=>⟨f t,hb.mapsTo t.property⟩
  have hF : Function.Bijective F := by
    constructor
    · intro x y h
      exact Subtype.ext (hb.injOn x.property y.property (congrArg Subtype.val h))
    · intro y
      obtain ⟨x,hx,he⟩ := hb.surjOn y.property
      exact ⟨⟨x,hx⟩,Subtype.ext he⟩
  let e : Icc a b ≃ Icc c d := Equiv.ofBijective F hF
  have hec : Continuous e := by
    exact (hc.domRestrict).subtype_mk _
  let H : Icc a b ≃ₜ Icc c d := hec.homeoOfEquivCompactToT2
  let clamp : ℝ → Icc c d := fun y=>⟨max c (min d y),le_max_left _ _,max_le hcd (min_le_left _ _)⟩
  have hcl : Continuous clamp := (continuous_const.max (continuous_const.min continuous_id)).subtype_mk _
  have hcl_eq (y : ℝ) (hy : y ∈ Icc c d) : (clamp y : ℝ)=y := by simp [clamp,max_eq_right hy.1,min_eq_right hy.2]
  let g : ℝ → ℝ := fun y=>H.symm (clamp y)
  refine ⟨g,continuous_subtype_val.comp (H.symm.continuous.comp hcl),fun y=>(H.symm (clamp y)).property,?_,?_⟩
  · intro y hy
    have h := congrArg Subtype.val (H.apply_symm_apply (clamp y))
    change f (g y)=(clamp y : ℝ) at h
    exact h.trans (hcl_eq y hy)
  · intro t ht
    have hclt : clamp (f t)=H ⟨t,ht⟩ := Subtype.ext (hcl_eq (f t) (hb.mapsTo ht))
    dsimp [g]
    rw [hclt,H.symm_apply_apply]
end QuinticLienard.RealAnalysis

end OAI
