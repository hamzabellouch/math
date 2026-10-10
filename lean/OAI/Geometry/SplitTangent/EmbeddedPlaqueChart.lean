import Mathlib

namespace OAI

/-! Embedded Plaque Chart. -/

noncomputable section
open Set Filter Topology
universe u v w
namespace EmbeddedPlaqueChart
variable {X : Type u} {A : Type v} {B : Type w}
  [TopologicalSpace X] [TopologicalSpace A] [TopologicalSpace B]

structure Data (Z : Set X) where
  ambient : OpenPartialHomeomorph X (A × B)
  U : Set A
  V : Set B
  open_U : IsOpen U
  open_V : IsOpen V
  rectangle : U ×ˢ V⊆ambient.target
  point : Z
  mem_source : point.val∈ambient.source
  mem_rectangle : ambient point.val∈U ×ˢ V
  saturated : ∀a∈U,ambient.symm (a,(ambient point.val).2)∈Z
  unique_transverse : ∀y∈Z,y∈ambient.source → ambient y∈U ×ˢ V →
    (ambient y).2=(ambient point.val).2

namespace Data
variable {Z : Set X} (D : Data (A := A) (B := B) Z)

def inverse (a : A) : Z := by
  classical
  exact if h : a∈D.U then
    ⟨D.ambient.symm (a,(D.ambient D.point.val).2),D.saturated a h⟩ else D.point

lemma inverse_val {a : A} (ha : a∈D.U) : (D.inverse a).val=D.ambient.symm (a,(D.ambient D.point.val).2) := by
  simp only [inverse,dite_eq_left ha]

lemma inverse_continuousAt {a : A} (ha : a∈D.U) : ContinuousAt D.inverse a := by
  apply IsInducing.subtypeVal.continuousAt_iff.mpr
  have ht : (a,(D.ambient D.point.val).2)∈D.ambient.target :=
    D.rectangle (show (a,(D.ambient D.point.val).2)∈D.U ×ˢ D.V from ⟨ha,D.mem_rectangle.2⟩)
  have hh := D.ambient.symm.continuousAt ht
  have hc : ContinuousAt (fun t : A => D.ambient.symm (t,(D.ambient D.point.val).2)) a :=
    hh.comp (f := fun t : A => (t,(D.ambient D.point.val).2)) (x := a)
      (continuousAt_id.prodMk continuousAt_const)
  apply hc.congr
  filter_upwards [D.open_U.mem_nhds ha] with t ht
  exact (D.inverse_val ht).symm

 
def chart : OpenPartialHomeomorph Z A where
  toFun y := (D.ambient y.val).1
  invFun := D.inverse
  source := {y | y.val∈D.ambient.source ∧ D.ambient y.val∈D.U ×ˢ D.V}
  target := D.U
  map_source' := by
    intro y hy
    exact hy.2.1
  map_target' := by
    intro a ha
    have ht : (a,(D.ambient D.point.val).2)∈D.ambient.target :=
      D.rectangle (show (a,(D.ambient D.point.val).2)∈D.U ×ˢ D.V from ⟨ha,D.mem_rectangle.2⟩)
    change (D.inverse a).val∈D.ambient.source ∧ D.ambient (D.inverse a).val∈D.U ×ˢ D.V
    rw [D.inverse_val ha,D.ambient.right_inv ht]
    exact ⟨D.ambient.map_target ht,ha,D.mem_rectangle.2⟩
  left_inv' := by
    intro y hy
    apply Subtype.ext
    rw [D.inverse_val hy.2.1]
    have hb := D.unique_transverse y.val y.property hy.1 hy.2
    have he : ((D.ambient y.val).1,(D.ambient D.point.val).2)=D.ambient y.val :=
      Prod.ext rfl hb.symm
    rw [he,D.ambient.left_inv hy.1]
  right_inv' := by
    intro a ha
    have ht : (a,(D.ambient D.point.val).2)∈D.ambient.target :=
      D.rectangle (show (a,(D.ambient D.point.val).2)∈D.U ×ˢ D.V from ⟨ha,D.mem_rectangle.2⟩)
    rw [D.inverse_val ha,D.ambient.right_inv ht]
  continuousOn_toFun := by
    intro y hy
    exact ((D.ambient.continuousAt hy.1).comp continuousAt_subtype_val).fst.continuousWithinAt
  continuousOn_invFun := fun _ ha => (D.inverse_continuousAt ha).continuousWithinAt
  open_source := (D.ambient.isOpen_inter_preimage (D.open_U.prod D.open_V)).preimage continuous_subtype_val
  open_target := D.open_U

lemma chart_mem : D.point∈D.chart.source := ⟨D.mem_source,D.mem_rectangle⟩
lemma chart_source {y : Z} : y∈D.chart.source ↔
    y.val∈D.ambient.source ∧ D.ambient y.val∈D.U ×ˢ D.V := Iff.rfl
lemma chart_target : D.chart.target=D.U := rfl
lemma chart_apply (y : Z) : D.chart y=(D.ambient y.val).1 := rfl
lemma chart_inverse_val {a : A} (ha : a∈D.chart.target) :
    (D.chart.symm a).val=D.ambient.symm (a,(D.ambient D.point.val).2) := D.inverse_val ha

end Data
end EmbeddedPlaqueChart

end

end OAI
