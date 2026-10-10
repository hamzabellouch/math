import Mathlib
import OAI.Geometry.Cannon.Beltrami.SideOrientation

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
open Set Topology
open Set Topology Filter Metric unitInterval
open scoped InnerProductSpace
open Set unitInterval
open Set Metric Topology
open Set Topology unitInterval

namespace CannonCharts

open unitInterval

def StripCrossing (q : I → Plane) : Prop :=
  Continuous q ∧ (q 0).1 = 1 ∧ (q 1).1 = 2 ∧
    ∀ t, (q t).1 ∈ Icc 1 2 ∧ |(q t).2| ≤ 2

def stripFamily {X : Type*} (e : Plane → X) : Set (Set X) :=
  {A | ∃ q : I → Plane, StripCrossing q ∧ A = range (e ∘ q)}

def macroFamily {X : Type*} [MetricSpace X] (d : ℝ) : Set (Set X) :=
  {A | ∃ p : I → X, Continuous p ∧ A = range p ∧ d ≤ diam A}

lemma stripFamily_nonempty {X : Type*} (e : Plane → X) : (stripFamily e).Nonempty := by
  let q : I → Plane := fun t => (1+(t:ℝ),0)
  refine ⟨range (e ∘ q),q,?_,rfl⟩
  refine ⟨by fun_prop,by norm_num [q],by norm_num [q],?_⟩
  intro t
  change (1+(t:ℝ)) ∈ Icc 1 2 ∧ |(0:ℝ)| ≤ 2
  constructor
  · constructor <;> nlinarith [t.property.1,t.property.2]
  · norm_num

lemma stripFamily_member_nonempty {X : Type*} {e : Plane → X} {A : Set X}
    (hA : A ∈ stripFamily e) : A.Nonempty := by
  obtain ⟨q,_,rfl⟩ := hA
  exact range_nonempty _

theorem finite_strip_localization {X : Type*} [MetricSpace X] [CompactSpace X]
    (φ : X ≃ₜ SphereTwo) (d : ℝ) (hd : 0 < d) :
    ∃ (J : Finset X) (e : (J × Fin 4) → Plane → X),
      J.Nonempty ∧ (∀ j, IsOpenEmbedding (e j)) ∧
      (∀ j, diam (e j '' box 8) < d) ∧
      ∀ A ∈ macroFamily (X := X) d,
        ∃ j, ∃ B ∈ stripFamily (e j), B ⊆ A := by
  classical
  obtain ⟨J,e,he,hdiam,hcover⟩ := finite_small_charts φ d hd
  obtain ⟨z,hz⟩ : (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr (by norm_num)
  obtain ⟨j,hj⟩ := hcover (φ.symm ⟨z,hz⟩)
  have hJ : J.Nonempty := ⟨j.val,j.property⟩
  let f : (J × Fin 4) → Plane → X := fun j => e j.1 ∘ (sideOrientation j.2).symm
  have hbox (j : Fin 4) : (sideOrientation j).symm '' box 8 = box 8 := by
    apply Subset.antisymm
    · rintro _ ⟨z,hz,rfl⟩
      have hn := norm_sideOrientation j ((sideOrientation j).symm z)
      rw [Homeomorph.apply_symm_apply] at hn
      simpa only [box, mem_closedBall, dist_zero_right, ← hn] using hz
    · intro z hz
      refine ⟨sideOrientation j z,?_,(sideOrientation j).symm_apply_apply z⟩
      simpa only [box,mem_closedBall,dist_zero_right,norm_sideOrientation] using hz
  refine ⟨J,f,hJ,fun j => (he j.1).comp (sideOrientation j.2).symm.isOpenEmbedding,?_,?_⟩
  · intro j
    rw [show f j '' box 8 = e j.1 '' box 8 by dsimp [f]; rw [image_comp,hbox]]
    exact hdiam j.1
  · rintro A ⟨p,hp,rfl,hmacro⟩
    obtain ⟨j,hj⟩ := hcover (p 0)
    have hout : ∃ t : I, p t ∉ e j '' box 8 := by
      by_contra hn
      push Not at hn
      have hrange : range p ⊆ e j '' box 8 := by rintro _ ⟨t,rfl⟩; exact hn t
      have hle := diam_mono hrange
        ((isCompact_closedBall (0:Plane) 8).image (he j).continuous).isBounded
      exact (not_lt_of_ge (hmacro.trans hle)) (hdiam j)
    obtain ⟨b,hb⟩ := hout
    let P : Path (p 0) (p 1) := ⟨⟨p,hp⟩,rfl,rfl⟩
    let Q := P.subpath 0 b
    have hzero : Q 0 ∈ e j '' openBox 1 := by rw [Q.source]; exact hj
    have hone : Q 1 ∉ e j '' box 2 := by
      rw [Q.target]
      intro h
      apply hb
      exact image_mono (closedBall_subset_closedBall (by norm_num : (2:ℝ) ≤ 8)) h
    obtain ⟨k,q,hq,hq0,hq1,hqmem,hsub⟩ :=
      chart_strip_crossing (e j) (he j) Q Q.continuous hzero hone
    refine ⟨(j,k),range (f (j,k) ∘ q),⟨q,⟨hq,hq0,hq1,hqmem⟩,rfl⟩,?_⟩
    apply hsub.trans
    rw [Path.range_subpath_of_le _ _ _ zero_le]
    exact image_subset_range _ _

end CannonCharts

end
end
end
end
end
end
end
end
end

end OAI
