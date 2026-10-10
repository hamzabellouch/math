import Mathlib

namespace OAI

section


/-! Uniform short exact lifts and uniform local metric preservation produce
an actual topological covering, with no assumed covering-space producer. -/
noncomputable section
open Set Metric
namespace HyperbolicObstruction
variable {E X : Type*} [MetricSpace E] [MetricSpace X]

structure UniformMetricCoverData (p : E → X) (r : ℝ) : Prop where
  positive : 0<r
  local_dist : ∀ a b, dist a b<4*r → dist (p a) (p b)=dist a b
  short_lift : ∀ a y, dist y (p a)<r → ∃ b, p b=y ∧ dist b a=dist y (p a)

namespace UniformMetricCoverData
variable {p : E → X} {r : ℝ} (h : UniformMetricCoverData p r)
include h

lemma continuous : Continuous p := by
  rw [Metric.continuous_iff]
  intro a ε hε
  refine ⟨min r ε,lt_min h.positive hε,fun b hb => ?_⟩
  rw [h.local_dist b a (by linarith [(lt_min_iff.mp hb).1,h.positive])]
  exact (lt_min_iff.mp hb).2

lemma nearby_unique {a b : E} (hab : dist a b<4*r) (he : p a=p b) : a=b := by
  apply dist_eq_zero.mp
  rw [←h.local_dist a b hab,he,dist_self]

lemma discrete_fiber (x : X) : DiscreteTopology (p ⁻¹' {x}) := by
  apply discreteTopology_iff_isOpen_singleton.mpr
  intro a
  apply Metric.isOpen_iff.mpr
  intro b hb
  have he : b=a := mem_singleton_iff.mp hb
  subst b
  refine ⟨r,h.positive,?_⟩
  intro b hb
  apply mem_singleton_iff.mpr
  apply Subtype.ext
  apply h.nearby_unique (by have hh : dist b.val a.val<r := hb; linarith [h.positive])
  exact b.property.trans a.property.symm

abbrev U (x : X) := ball x (r/4)
abbrev F (x : X) := p ⁻¹' ({x} : Set X)
abbrev V (x : X) := p ⁻¹' U (r:=r) x

lemma recenter_exists (x : X) (a : V (p:=p) (r:=r) x) :
    ∃ b : F (p:=p) x, dist b.val a.val=dist (p a.val) x := by
  obtain ⟨b,hb,hba⟩ := h.short_lift a.val x (by
    have hh : dist (p a.val) x<r/4 := a.property
    rw [dist_comm]; linarith [h.positive])
  exact ⟨⟨b,hb⟩,by rw [hba,dist_comm]⟩

def recenter (x : X) (a : V (p:=p) (r:=r) x) : F (p:=p) x := (h.recenter_exists x a).choose
lemma recenter_dist (x : X) (a : V (p:=p) (r:=r) x) :
    dist (h.recenter x a).val a.val=dist (p a.val) x := (h.recenter_exists x a).choose_spec

lemma recenter_eq {x : X} (a b : V (p:=p) (r:=r) x) (hab : dist a b<r) :
    h.recenter x a=h.recenter x b := by
  apply Subtype.ext
  apply h.nearby_unique
  · have hh := dist_triangle4 (h.recenter x a).val a.val b.val (h.recenter x b).val
    rw [h.recenter_dist,dist_comm b.val _,h.recenter_dist] at hh
    have ha : dist (p a.val) x<r/4 := a.property
    have hb : dist (p b.val) x<r/4 := b.property
    change dist a.val b.val<r at hab
    linarith [h.positive]
  · exact (h.recenter x a).property.trans (h.recenter x b).property.symm

lemma recenter_continuous (x : X) : Continuous (h.recenter x) := by
  rw [Metric.continuous_iff]
  intro a ε hε
  refine ⟨r,h.positive,fun b hb => ?_⟩
  rw [h.recenter_eq b a hb,dist_self]
  exact hε

lemma out_exists (x : X) (a : F (p:=p) x) (y : U (r:=r) x) :
    ∃ b : V (p:=p) (r:=r) x, p b.val=y.val ∧ dist b.val a.val=dist y.val x := by
  have hy : dist y.val x<r/4 := y.property
  obtain ⟨b,hb,hba⟩ := h.short_lift a.val y.val (by rw [a.property]; linarith [h.positive])
  refine ⟨⟨b,by change p b ∈ U (r:=r) x; rw [hb]; exact y.property⟩,hb,?_⟩
  have hae : p a.val=x := a.property
  simpa only [hae] using hba

def out (x : X) (a : F (p:=p) x) (y : U (r:=r) x) : V (p:=p) (r:=r) x :=
  (h.out_exists x a y).choose
lemma out_proj (x : X) (a : F (p:=p) x) (y : U (r:=r) x) : p (h.out x a y).val=y.val :=
  (h.out_exists x a y).choose_spec.1
lemma out_dist (x : X) (a : F (p:=p) x) (y : U (r:=r) x) :
    dist (h.out x a y).val a.val=dist y.val x := (h.out_exists x a y).choose_spec.2

lemma out_isometry (x : X) (a : F (p:=p) x) : Isometry (h.out x a) := by
  apply Isometry.of_dist_eq
  intro y z
  have hh := dist_triangle (h.out x a y).val a.val (h.out x a z).val
  rw [h.out_dist,dist_comm a.val _,h.out_dist] at hh
  have hy : dist y.val x<r/4 := y.property
  have hz : dist z.val x<r/4 := z.property
  change dist (h.out x a y).val (h.out x a z).val=dist y.val z.val
  rw [←h.local_dist _ _ (by linarith [h.positive]),h.out_proj,h.out_proj]

lemma out_recenter (x : X) (a : V (p:=p) (r:=r) x) :
    h.out x (h.recenter x a) ⟨p a.val,a.property⟩=a := by
  apply Subtype.ext
  apply h.nearby_unique
  · have hh := dist_triangle (h.out x (h.recenter x a) ⟨p a.val,a.property⟩).val (h.recenter x a).val a.val
    rw [h.out_dist,h.recenter_dist] at hh
    have ha : dist (p a.val) x<r/4 := a.property
    linarith [h.positive]
  · exact h.out_proj _ _ _

lemma recenter_out (x : X) (a : F (p:=p) x) (y : U (r:=r) x) :
    h.recenter x (h.out x a y)=a := by
  apply Subtype.ext
  apply h.nearby_unique
  · have hh := dist_triangle (h.recenter x (h.out x a y)).val (h.out x a y).val a.val
    rw [h.recenter_dist,h.out_proj,h.out_dist] at hh
    have hy : dist y.val x<r/4 := y.property
    linarith [h.positive]
  · exact (h.recenter x (h.out x a y)).property.trans a.property.symm

def homeomorph (x : X) : V (p:=p) (r:=r) x ≃ₜ U (r:=r) x × F (p:=p) x := by
  letI : DiscreteTopology (F (p:=p) x) := h.discrete_fiber x
  exact
  { toFun := fun a => (⟨p a.val,a.property⟩,h.recenter x a)
    invFun := fun q => h.out x q.2 q.1
    left_inv := h.out_recenter x
    right_inv := fun ⟨y,a⟩ => Prod.ext (Subtype.ext (h.out_proj x a y)) (h.recenter_out x a y)
    continuous_toFun := ((h.continuous.comp continuous_subtype_val).subtype_mk _).prodMk (h.recenter_continuous x)
    continuous_invFun := continuous_prod_of_discrete_right.mpr (fun a => (h.out_isometry x a).continuous) }

lemma isCoveringMap : IsCoveringMap p := by
  intro x
  refine ⟨h.discrete_fiber x,U (r:=r) x,mem_ball_self (by linarith [h.positive]),isOpen_ball,
    isOpen_ball.preimage h.continuous,h.homeomorph x,?_⟩
  intro a
  rfl

end UniformMetricCoverData
end HyperbolicObstruction
end
end

section

end

end OAI
