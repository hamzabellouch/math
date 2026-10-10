import Mathlib
import OAI.Analysis.HardSphere.Conditioning.RoutePartition

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Comparison CellOrbital
attribute [local instance] Classical.propDecidable
variable {J : Type*} [Fintype J] [DecidableEq J]

def slotCenter {K : ℕ} (home : J→Fin 3→Fin K) (v : Fin 3→Fin K) : Option J→Fin 3→Fin K :=
  fun i ↦ i.elim v home

omit [Fintype J] [DecidableEq J] in
lemma routeEmbedding_center {K n : ℕ} (home : J→Fin 3→Fin K)
    (labels : Fin n↪J) (v : Fin (n+1)→Fin 3→Fin K)
    (hh : ∀i,home (labels i)=v i.castSucc) (i : Fin (n+1)) :
    slotCenter home (v (Fin.last n)) (routeEmbedding labels i)=v i := by
  by_cases hi : i.val<n
  · have he : i=(⟨i.val,hi⟩ : Fin n).castSucc := Fin.ext rfl
    rw [he,routeEmbedding_castSucc]
    exact hh _
  · have he : i=Fin.last n := Fin.ext (by simp only [Fin.val_last]; omega)
    rw [he,routeEmbedding_last]
    rfl

omit [Fintype J] [DecidableEq J] in
lemma route_two_center_bounds {K n : ℕ} {L : Length}
    (home : J→Fin 3→Fin K) (labels : Fin (n+1)↪J)
    (v : Fin (n+2)→Fin 3→Fin K)
    (hh : ∀i,home (labels i)=v i.castSucc)
    (ha : ∀i : Fin (n+1),torusDistance L (gridCenter L (v i.castSucc))
      (gridCenter L (v i.succ))≤1) :
    (∀j,torusDistance L (gridCenter L (home j))
      (gridCenter L (slotCenter home (v (Fin.last (n+1))) (routePermutation labels (some j))))≤1) ∧
    (∀j,torusDistance L (gridCenter L (home j))
      (gridCenter L (slotCenter home (v 0) ((routePermutation labels).symm (some j))))≤1) := by
  have hf : ∀j,torusDistance L (gridCenter L (home j))
      (gridCenter L (slotCenter home (v (Fin.last (n+1))) (routePermutation labels (some j))))≤1 := by
    intro j
    by_cases hj : ∃i,labels i=j
    · obtain ⟨i,rfl⟩ := hj
      rw [routePermutation_label,routeEmbedding_center home labels v hh,hh i]
      exact ha i
    · have hnot : some j∉routeSlots labels := by
        rw [routeSlots_exact]
        simp only [Finset.mem_insert,Option.some_ne_none,Finset.mem_image,Finset.mem_univ,
          true_and,false_or,not_exists]
        intro i hi
        exact hj ⟨i,Option.some.inj hi⟩
      rw [routePermutation_fixed labels _ hnot]
      change torusDistance L (gridCenter L (home j)) (gridCenter L (home j))≤1
      simp [torusDistance]
  refine ⟨hf,?_⟩
  intro j
  cases he : (routePermutation labels).symm (some j) with
  | none =>
    have hj : j=labels 0 := by
      have hh' := congrArg (routePermutation labels) he
      rw [Equiv.apply_symm_apply,routePermutation_star] at hh'
      exact Option.some.inj hh'
    rw [hj,hh 0]
    change torusDistance L (gridCenter L (v 0)) (gridCenter L (v 0))≤1
    simp [torusDistance]
  | some k =>
    have hek : routePermutation labels (some k)=some j := by
      rw [←he,Equiv.apply_symm_apply]
    have hk := hf k
    rw [hek] at hk
    change torusDistance L (gridCenter L (home j)) (gridCenter L (home k))≤1
    change torusDistance L (gridCenter L (home k)) (gridCenter L (home j))≤1 at hk
    rw [torusDistance_comm]
    exact hk

lemma slotCenter_fiber {K : ℕ} (home : J→Fin 3→Fin K) (v : Fin 3→Fin K)
    (M : ℕ) (hm : ∀w,(Finset.univ.filter (fun j ↦ home j=w)).card≤M) (w : Fin 3→Fin K) :
    (Finset.univ.filter (fun i ↦ slotCenter home v i=w)).card≤M+1 := by
  have hs : Finset.univ.filter (fun i ↦ slotCenter home v i=w) ⊆
      insert none ((Finset.univ.filter (fun j ↦ home j=w)).image some) := by
    intro i hi
    cases i with
    | none => exact Finset.mem_insert_self _ _
    | some j =>
      exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j,Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2⟩,rfl⟩)
  exact (Finset.card_le_card hs).trans ((Finset.card_insert_le _ _).trans
    (Nat.add_le_add_right (Finset.card_image_le.trans (hm w)) 1))

end HardSphere.Groups
end
end

end OAI
