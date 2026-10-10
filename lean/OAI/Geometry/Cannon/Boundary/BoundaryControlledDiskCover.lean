import Mathlib
import OAI.Geometry.Cannon.PlaneTopology.ControlledDiskCover

namespace OAI

section
section
section
section
namespace CannonRelease
open CannonGraph CannonVisual CannonRegularDisk Set Metric

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)
attribute [local instance] Classical.propDecidable

theorem boundary_controlled_disk_cover (φ : Boundary D ≃ₜ SphereTwo) :
    let _ := visualMetricSpace D hδ
    ∃ c : ℝ, 0<c ∧ c≤1 ∧ ∃ B : ℕ, ∀ s : ℝ, 0<s → s≤1/2 →
      ∃ (T : Finset (Boundary D)) (U : T → Set (Boundary D)),
        (∀ i j : T, i≠j → (c/2)*s≤dist i.val j.val) ∧
        (∀ i, IsRegularDisk (U i) ∧ ball i.val (c*s) ⊆ U i ∧ closure (U i) ⊆ ball i.val s) ∧
        (∀ x : Boundary D, ∃ i, x ∈ U i) ∧
        (∀ i, ((Finset.univ : Finset T).filter (fun j => (closure (U i) ∩ closure (U j)).Nonempty)).card≤B) ∧
        ∀ x : Boundary D, ((Finset.univ : Finset T).filter (fun i => x ∈ closure (U i))).card≤B := by
  let _ := visualMetricSpace D hδ
  dsimp only
  obtain ⟨c,hc,hc1,hdisks⟩ := boundary_controlled_regular_disks D hδ φ
  obtain ⟨Q,C,_,_,hpack⟩ := relative_polynomial_packing D hδ
  exact ⟨c,hc,hc1,controlled_disk_cover hpack hc hc1 hdisks⟩

end CannonRelease

end
section
noncomputable section
namespace CannonDiskColoring
open Set Finset

attribute [local instance] Classical.propDecidable

lemma finite_relation_coloring {I : Type*} [Fintype I]
    (R : I → I → Prop) (hsym : ∀ ⦃left right⦄, R left right → R right left) {B : ℕ}
    (hdegree : ∀ i, ((Finset.univ : Finset I).filter (R i)).card ≤ B) :
    ∃ color : I → Fin (B+1), ∀ i j, i≠j → R i j → color i≠color j := by
  classical
  suffices ∀ S : Finset I, ∃ color : I → Fin (B+1),
      ∀ i∈S, ∀ j∈S, i≠j → R i j → color i≠color j by
    obtain ⟨color,h⟩ := this Finset.univ
    exact ⟨color,fun i j => h i (mem_univ _) j (mem_univ _)⟩
  intro S
  induction S using Finset.induction_on with
  | empty => exact ⟨fun _ => 0,by simp⟩
  | @insert a S ha ih =>
    obtain ⟨c,hc⟩ := ih
    let N := S.filter (R a)
    have hN : N.card ≤ B := (Finset.card_le_card (by
      intro i hi
      exact mem_filter.mpr ⟨mem_univ i,(mem_filter.mp hi).2⟩)).trans (hdegree a)
    have hn : (N.image c).card < Fintype.card (Fin (B+1)) := by
      have hh := (card_image_le (s:=N) (f:=c)).trans hN
      simpa only [Fintype.card_fin] using Nat.lt_succ_of_le hh
    obtain ⟨v,_,hv⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (t:=Finset.univ) (by simpa only [card_univ] using hn)
    let d := Function.update c a v
    refine ⟨d,?_⟩
    intro i hi j hj hij hR
    by_cases hia : i=a
    · subst i
      have hja : j≠a := Ne.symm hij
      have hjS : j∈S := (Finset.mem_insert.mp hj).resolve_left hja
      have hcv : c j≠v := by
        intro h
        apply hv
        rw [←h]
        exact Finset.mem_image_of_mem c (Finset.mem_filter.mpr ⟨hjS,hR⟩)
      simpa only [d,Function.update_self,Function.update_of_ne hja] using hcv.symm
    · have hiS : i∈S := (Finset.mem_insert.mp hi).resolve_left hia
      by_cases hja : j=a
      · subst j
        have hcv : c i≠v := by
          intro h
          apply hv
          rw [←h]
          exact Finset.mem_image_of_mem c (Finset.mem_filter.mpr ⟨hiS,hsym hR⟩)
        simpa only [d,Function.update_self,Function.update_of_ne hia] using hcv
      · have hjS : j∈S := (Finset.mem_insert.mp hj).resolve_left hja
        simpa only [d,Function.update_of_ne hia,Function.update_of_ne hja] using hc i hiS j hjS hij hR

theorem bounded_intersection_coloring {I X : Type*} [Fintype I]
    (K : I → Set X) {B : ℕ}
    (hdegree : ∀ i, ((Finset.univ : Finset I).filter
      (fun j => (K i ∩ K j).Nonempty)).card ≤ B) :
    ∃ color : I → Fin (B+1), ∀ i j, i≠j → color i=color j → Disjoint (K i) (K j) := by
  classical
  obtain ⟨c,hc⟩ := finite_relation_coloring (fun i j => (K i ∩ K j).Nonempty)
    (fun _ _ h => by simpa only [Set.inter_comm] using h) hdegree
  refine ⟨c,?_⟩
  intro i j hij he
  rw [Set.disjoint_iff_inter_eq_empty]
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact hc i j hij ⟨x,hx⟩ he

end CannonDiskColoring

end
end
namespace CannonRelease
open CannonGraph CannonVisual CannonRegularDisk Set Metric

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)
attribute [local instance] Classical.propDecidable

theorem boundary_disjoint_disk_stages (φ : Boundary D ≃ₜ SphereTwo) :
    let _ := visualMetricSpace D hδ
    ∃ c : ℝ, 0<c ∧ c ≤ 1 ∧ ∃ B : ℕ, ∀ s : ℝ, 0<s → s ≤ 1/2 →
      ∃ (T : Finset (Boundary D)) (U : T → Set (Boundary D)) (color : T → Fin B),
        (∀ i j : T, i≠j → (c/2)*s ≤ dist i.val j.val) ∧
        (∀ i, IsRegularDisk (U i) ∧ ball i.val (c*s) ⊆ U i ∧ closure (U i) ⊆ ball i.val s) ∧
        (∀ x : Boundary D, ∃ i, x∈U i) ∧
        ∀ i j : T, i≠j → color i=color j → Disjoint (closure (U i)) (closure (U j)) := by
  let _ := visualMetricSpace D hδ
  dsimp only
  obtain ⟨c,hc,hc1,B,hB⟩ := boundary_controlled_disk_cover D hδ φ
  refine ⟨c,hc,hc1,B+1,?_⟩
  intro s hs hs1
  obtain ⟨T,U,hsep,hdisks,hcover,hdegree,_⟩ := hB s hs hs1
  obtain ⟨color,hcolor⟩ := CannonDiskColoring.bounded_intersection_coloring
    (fun i : T => closure (U i)) hdegree
  exact ⟨T,U,color,hsep,hdisks,hcover,hcolor⟩

end CannonRelease

end
end
end

end OAI
