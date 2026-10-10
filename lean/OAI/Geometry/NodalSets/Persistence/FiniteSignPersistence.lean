import Mathlib.Topology.Order.Compact
import OAI.Geometry.NodalSets.Hausdorff.FiniteNodalCylinder

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set MeasureTheory
open scoped ENNReal
noncomputable section

lemma compact_positive_margin {E : Type*} [TopologicalSpace E] {K : Set E}
    (hK : IsCompact K) (f : E → ℝ) (hf : ContinuousOn f K) (hp : ∀ x ∈ K, 0 < f x) :
    ∃ ε > 0, ∀ x ∈ K, ε ≤ f x := by
  rcases K.eq_empty_or_nonempty with h | h
  · refine ⟨1,by norm_num,?_⟩
    simp [h]
  · obtain ⟨x,hx,hmin⟩ := hK.exists_isMinOn h hf
    exact ⟨f x,hp x hx,fun y hy ↦ hmin hy⟩

lemma finite_sign_uniform_persistence {ι : Type*} (t : Finset ι)
    (P N : ι → Set Coord) (hP : ∀ i ∈ t, IsCompact (P i)) (hN : ∀ i ∈ t, IsCompact (N i))
    (f : Coord → ℝ) (hf : Continuous f)
    (hsign : ∀ i ∈ t, (∀ x ∈ P i, 0 < f x) ∧ (∀ x ∈ N i, f x < 0)) :
    ∃ ε > 0, ∀ g : Coord → ℝ,
      (∀ i ∈ t, ∀ x ∈ P i ∪ N i, |g x-f x| < ε) →
      ∀ i ∈ t, (∀ x ∈ P i, 0 < g x) ∧ (∀ x ∈ N i, g x < 0) := by
  have hp : ∀ x ∈ ⋃ i ∈ t, P i, 0 < f x := by
    intro x hx
    obtain ⟨i,hi,hx⟩ := mem_iUnion₂.mp hx
    exact (hsign i hi).1 x hx
  have hn : ∀ x ∈ ⋃ i ∈ t, N i, 0 < -f x := by
    intro x hx
    obtain ⟨i,hi,hx⟩ := mem_iUnion₂.mp hx
    exact neg_pos.mpr ((hsign i hi).2 x hx)
  obtain ⟨εp,hεp,hpm⟩ := compact_positive_margin (t.isCompact_biUnion hP) f hf.continuousOn hp
  obtain ⟨εn,hεn,hnm⟩ := compact_positive_margin (t.isCompact_biUnion hN) (fun x ↦ -f x) hf.neg.continuousOn hn
  refine ⟨min εp εn,lt_min hεp hεn,?_⟩
  intro g hg i hi
  constructor
  · intro x hx
    have hm := hpm x (mem_iUnion₂.mpr ⟨i,hi,hx⟩)
    have he := abs_lt.mp (hg i hi x (Or.inl hx))
    have hh := min_le_left εp εn
    linarith
  · intro x hx
    have hm := hnm x (mem_iUnion₂.mpr ⟨i,hi,hx⟩)
    have he := abs_lt.mp (hg i hi x (Or.inr hx))
    have hh := min_le_right εp εn
    linarith

lemma finite_nodal_cylinder_persistence {ι : Type*} (t : Finset ι)
    (f : Coord → ℝ) (hf : Continuous f) (x : ι → Coord) (R : ι → ℝ) (j : ι → Fin 4)
    {U : Set Coord} {tau r : ℝ} (ht : 0 ≤ tau) (hr : 0 ≤ r) (htr : tau+r ≤ 1)
    (hR : ∀ i ∈ t, 0 < R i)
    (hdis : (↑t : Set ι).PairwiseDisjoint (fun i ↦ sourceClosedBall (x i) (R i)))
    (hU : ∀ i ∈ t, sourceClosedBall (x i) (R i) ⊆ U)
    (hsign : ∀ i ∈ t,
      (∀ y ∈ sourceClosedBall (x i) (r*R i), 0 < f y) ∧
      (∀ y ∈ sourceClosedBall (x i+R i • (tau • Pi.single (j i) 1)) (r*R i), f y < 0)) :
    ∃ ε > 0, ∀ g : Coord → ℝ, Continuous g →
      (∀ i ∈ t, ∀ y ∈ sourceClosedBall (x i) (r*R i) ∪
        sourceClosedBall (x i+R i • (tau • Pi.single (j i) 1)) (r*R i), |g y-f y| < ε) →
      ENNReal.ofReal (2*r^3*∑ i ∈ t, (R i)^3) ≤
        Measure.hausdorffMeasure (4:ℝ) ((U ×ˢ Icc (-1:ℝ) 1) ∩ {y : Coord × ℝ | g y.1 = 0}) := by
  obtain ⟨ε,hε,hpersist⟩ := finite_sign_uniform_persistence t
    (fun i ↦ sourceClosedBall (x i) (r*R i))
    (fun i ↦ sourceClosedBall (x i+R i • (tau • Pi.single (j i) 1)) (r*R i))
    (fun i _ ↦ sourceClosedBall_isCompact _ _) (fun i _ ↦ sourceClosedBall_isCompact _ _)
    f hf hsign
  refine ⟨ε,hε,?_⟩
  intro g hg hclose
  exact finite_nodal_cylinder_measure t g hg x R j ht hr htr hR hdis hU (hpersist g hclose)

end
end Yau.Geometry

end OAI
