import Mathlib
import OAI.Combinatorics.KMedian.Optimization.FractionalDual

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset
variable {n : ℕ}

def firstNearest (U : Finset (Fin n)) (d : Fin n → ℚ) (hU : U.Nonempty) : Fin n :=
  let m := (U.image d).min' (hU.image _)
  let B := U.filter (fun i => d i=m)
  have hB : B.Nonempty := by
    obtain ⟨a,ha,he⟩ := mem_image.mp (min'_mem (U.image d) (hU.image _))
    exact ⟨a,mem_filter.mpr ⟨ha,he⟩⟩
  B.min' hB

theorem firstNearest_spec (U : Finset (Fin n)) (d : Fin n → ℚ) (hU : U.Nonempty) :
    firstNearest U d hU ∈ U ∧ ∀ i ∈ U, d (firstNearest U d hU) ≤ d i := by
  let B := U.filter (fun i => d i=(U.image d).min' (hU.image _))
  have hB : B.Nonempty := by
    obtain ⟨a,ha,he⟩ := mem_image.mp (min'_mem (U.image d) (hU.image _))
    exact ⟨a,mem_filter.mpr ⟨ha,he⟩⟩
  change B.min' hB ∈ U ∧ ∀ i ∈ U, d (B.min' hB) ≤ d i
  have hh := mem_filter.mp (min'_mem B hB)
  refine ⟨hh.1,?_⟩
  intro i hi
  rw [hh.2]
  exact min'_le _ _ (mem_image.mpr ⟨i,hi,rfl⟩)

structure Filling (U : Finset (Fin n)) (y d : Fin n → ℚ) (t : ℚ) where
  amount : Fin n → ℚ
  outside : ∀ i, i ∉ U → amount i=0
  bounds : ∀ i ∈ U, 0 ≤ amount i ∧ amount i ≤ y i
  total : ∑ i ∈ U, amount i=t
  ordered : ∀ i ∈ U, ∀ a ∈ U, 0 < amount i → amount a < y a → d i ≤ d a

def fill (U : Finset (Fin n)) (y d : Fin n → ℚ) (t : ℚ)
    (hy : ∀ i ∈ U, 0 ≤ y i) (ht : 0 ≤ t) (hm : t ≤ ∑ i ∈ U, y i) : Filling U y d t := by
  if hU : U.Nonempty then
    let a := firstNearest U d hU
    have ha : a ∈ U := (firstNearest_spec U d hU).1
    have hmin : ∀ i ∈ U, d a ≤ d i := (firstNearest_spec U d hU).2
    if hsmall : t ≤ y a then
      let x : Fin n → ℚ := fun i => if i=a then t else 0
      refine ⟨x,?_,?_,?_,?_⟩
      · intro i hi
        exact ite_eq_right (fun (he : i=a) => hi (he.symm ▸ ha))
      · intro i hi
        by_cases he : i=a
        · subst i
          simpa only [x,ite_eq_left rfl] using And.intro ht hsmall
        · simp only [x,ite_eq_right he]
          exact ⟨le_rfl,hy i hi⟩
      · simp only [x,sum_ite_eq',ite_eq_left ha]
      · intro i hi b hb hix _
        have hei : i=a := by
          by_contra he
          simp only [x,ite_eq_right he,lt_self_iff_false] at hix
        subst i
        exact hmin b hb
    else
      have hlt : y a < t := lt_of_not_ge hsmall
      have hm' : t-y a ≤ ∑ i ∈ U.erase a, y i := by
        have hs := sum_erase_add U y ha
        linarith only [hm,hs]
      let z := fill (U.erase a) y d (t-y a) (fun i hi => hy i (mem_of_mem_erase hi))
        (sub_nonneg.mpr hlt.le) hm'
      let x : Fin n → ℚ := Function.update z.amount a (y a)
      have hxa : x a=y a := Function.update_self _ _ _
      have hxi : ∀ i, i ≠ a → x i=z.amount i := fun i hi => Function.update_of_ne hi _ _
      refine ⟨x,?_,?_,?_,?_⟩
      · intro i hi
        rw [hxi i (fun (he : i=a) => hi (he.symm ▸ ha))]
        exact z.outside i (fun he => hi (mem_of_mem_erase he))
      · intro i hi
        by_cases he : i=a
        · subst i; rw [hxa]; exact ⟨hy a ha,le_rfl⟩
        · rw [hxi i he]
          exact z.bounds i (mem_erase.mpr ⟨he,hi⟩)
      · rw [← sum_erase_add U x ha,hxa]
        have he : (∑ i ∈ U.erase a, x i)=∑ i ∈ U.erase a, z.amount i :=
          sum_congr rfl (fun i hi => hxi i (mem_erase.mp hi).1)
        rw [he,z.total]
        ring
      · intro i hi b hb hix hbx
        by_cases he : i=a
        · subst i; exact hmin b hb
        · have hbe : b ≠ a := by
            intro hb'; subst b; rw [hxa] at hbx; exact lt_irrefl _ hbx
          rw [hxi i he] at hix
          rw [hxi b hbe] at hbx
          exact z.ordered i (mem_erase.mpr ⟨he,hi⟩) b (mem_erase.mpr ⟨hbe,hb⟩) hix hbx
  else
    have he : U=∅ := not_nonempty_iff_eq_empty.mp hU
    have ht0 : t=0 := le_antisymm (by simpa only [he,sum_empty] using hm) ht
    refine ⟨fun _ => 0,fun _ _ => rfl,?_,?_,?_⟩ <;> simp [he,ht0]
termination_by U.card
decreasing_by exact card_erase_lt_of_mem ha

def computedNearest (y d : Fin n → ℚ) (hy : ∀ i, 0 ≤ y i) (hm : 1 ≤ ∑ i, y i) : Vector ℚ n :=
  Vector.ofFn (fill univ y d 1 (fun i _ => hy i) (by norm_num) hm).amount

theorem computedNearest_spec (y d : Fin n → ℚ) (hy : ∀ i, 0 ≤ y i) (hm : 1 ≤ ∑ i, y i)
    (H : ℚ) :
    let x := computedNearest y d hy hm
    (∀ i : Fin n, 0 ≤ x[i.val] ∧ x[i.val] ≤ y i) ∧
    (∑ i : Fin n, x[i.val])=1 ∧
    (∑ i : Fin n, x[i.val]*d i)=FractionalDual.value d y H := by
  let a := fill univ y d 1 (fun i _ => hy i) (by norm_num) hm
  have hx := fun i => a.bounds i (mem_univ _)
  have hs := a.total
  have ho := fun i j => a.ordered i (mem_univ _) j (mem_univ _)
  dsimp only [computedNearest]
  simp only [Vector.getElem_ofFn]
  refine ⟨hx,hs,le_antisymm ?_ (FractionalDual.value_le_assignment d y a.amount H hx hs)⟩
  obtain ⟨i,hi⟩ := FractionalDual.ordered_attains d y a.amount hx hs ho
  rw [← hi]
  exact FractionalDual.affine_le_value d y H (d i) (by simp [FractionalDual.thresholds])

end MetricKMedian.Preparation
end
end

end OAI
