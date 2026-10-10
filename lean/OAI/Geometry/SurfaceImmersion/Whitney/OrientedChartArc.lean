import OAI.Geometry.SurfaceImmersion.Whitney.SmoothDoubleTransitions
import Mathlib.Topology.Order.IntermediateValue

namespace OAI

/-! An embedded compact arc lying in one real chart has an oriented smooth
coordinate parameterization with exactly the original image and endpoints. -/
noncomputable section
open Set Filter
open scoped Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing

variable {N : Type*} [TopologicalSpace N]

theorem oriented_chart_arc (c : OpenPartialHomeomorph N ℝ) {γ : ℝ → N}
    {a b : ℝ} (hab : a < b) (hγ : ContinuousOn γ (Icc a b))
    (hinj : InjOn γ (Icc a b)) (hsource : MapsTo γ (Icc a b) c.source) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
      let u := s * c (γ a)
      let v := s * c (γ b)
      u < v ∧
      (∀ t ∈ Icc u v, s * t ∈ c.target) ∧
      (fun t => c.symm (s * t)) '' Icc u v = γ '' Icc a b ∧
      (Icc u v).InjOn (fun t => c.symm (s * t)) ∧
      c.symm (s * u) = γ a ∧ c.symm (s * v) = γ b := by
  have ha : a ∈ Icc a b := left_mem_Icc.mpr hab.le
  have hb : b ∈ Icc a b := right_mem_Icc.mpr hab.le
  have hc : ContinuousOn (fun t => c (γ t)) (Icc a b) :=
    c.continuousOn.comp hγ hsource
  have hi : InjOn (fun t => c (γ t)) (Icc a b) :=
    c.injOn.comp hinj hsource
  have hs : ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
      StrictMonoOn (fun t => s * c (γ t)) (Icc a b) := by
    rcases hc.strictMonoOn_of_injOn_Icc' hab.le hi with hm | hm
    · exact ⟨1,Or.inl rfl,by simpa only [one_mul] using hm⟩
    · refine ⟨-1,Or.inr rfl,?_⟩
      intro x hx y hy hxy
      simpa only [neg_one_mul,neg_lt_neg_iff] using hm hx hy hxy
  obtain ⟨s,hs,hm⟩ := hs
  have hss : s*s = 1 := by rcases hs with rfl | rfl <;> norm_num
  have hs0 : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
  have himage : (fun t => s * c (γ t)) '' Icc a b =
      Icc (s*c (γ a)) (s*c (γ b)) :=
    (continuousOn_const.mul hc).image_Icc_of_monotoneOn hab.le hm.monotoneOn
  have htarget : ∀ t ∈ Icc (s*c (γ a)) (s*c (γ b)), s*t ∈ c.target := by
    intro t ht
    obtain ⟨x,hx,rfl⟩ := himage.symm.subset ht
    simpa only [← mul_assoc,hss,one_mul] using c.map_source (hsource hx)
  refine ⟨s,hs,hm ha hb hab,htarget,?_,?_,?_,?_⟩
  · apply Set.Subset.antisymm
    · rintro y ⟨t,ht,rfl⟩
      obtain ⟨x,hx,rfl⟩ := himage.symm.subset ht
      refine ⟨x,hx,?_⟩
      dsimp only
      rw [← mul_assoc,hss,one_mul,c.left_inv (hsource hx)]
    · rintro y ⟨x,hx,rfl⟩
      refine ⟨s*c (γ x),himage.subset ⟨x,hx,rfl⟩,?_⟩
      dsimp only
      rw [← mul_assoc,hss,one_mul,c.left_inv (hsource hx)]
  · intro x hx y hy he
    exact mul_left_cancel₀ hs0 (c.symm.injOn (htarget x hx) (htarget y hy) he)
  · rw [← mul_assoc,hss,one_mul,c.left_inv (hsource ha)]
  · rw [← mul_assoc,hss,one_mul,c.left_inv (hsource hb)]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
