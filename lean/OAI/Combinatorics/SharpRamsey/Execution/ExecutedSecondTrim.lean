import Mathlib
import OAI.Combinatorics.SharpRamsey.Execution.ExecutedTrim

namespace OAI

section
namespace SharpLogRamsey.FreshExecution
open Finset BinaryTree TreeDecoder PublicTables
open scoped Classical BigOperators
noncomputable section
variable {I A B C : Type*} [DecidableEq I] {α : I→Type*}

def rightPath (target : I) : BinaryTree I→Finset I
  | .nil=>∅
  | .node i l r=>if i=target then ∅ else
      if target∈labels r then insert i (rightPath target r) else rightPath target l

lemma rightPath_subset (target : I) (t : BinaryTree I) : rightPath target t⊆labels t := by
  induction t with
  | nil=>exact empty_subset _
  | node i l r hl hr=>
    rw [rightPath,labels_node]
    split_ifs with hi hj
    · exact empty_subset _
    · exact insert_subset_insert i (hr.trans subset_union_right)
    · exact hl.trans (subset_union_left.trans (subset_insert _ _))

lemma rightPath_card (target : I) (t : BinaryTree I) :
    (rightPath target t).card≤t.height := by
  induction t with
  | nil=>rfl
  | node i l r hl hr=>
    rw [rightPath]
    split_ifs
    · exact Nat.zero_le _
    · exact (card_insert_le _ _).trans (by simp only [height]; omega)
    · simp only [height]; omega

def secondLoss (choose : ∀ i,α i→Domains A B→Option C)
    (mask : ∀ i,α i→CapReader A B C) (Y : Finset B)
    (i : I) (U : Domains A B) (x : α i) : ℝ :=
  match choose i x U with
  | none=>0
  | some c=>((Y\(mask i x U c).2).card:ℝ)

omit [DecidableEq I] in
lemma secondLoss_nonneg (choose : ∀ i,α i→Domains A B→Option C)
    (mask : ∀ i,α i→CapReader A B C) (Y : Finset B)
    (i : I) (U : Domains A B) (x : α i) : 0 ≤ secondLoss choose mask Y i U x := by
  unfold secondLoss
  cases choose i x U <;> positivity

theorem reached_second_loss (choose : ∀ i,α i→Domains A B→Option C)
    (read mask : ∀ i,α i→CapReader A B C)
    (hread : ∀ i x U c,(read i x U c).2=U.2∩(mask i x U c).2)
    (z : ∀ i,α i) (target : I) (Y : Finset B)
    (t : BinaryTree I) (U V : Domains A B) (ht : Separated t)
    (hmem : target∈labels t) (hv : arrive choose read z target t U=some V) :
    ((Y\V.2).card:ℝ)≤((Y\U.2).card:ℝ)+
      ∑ j∈rightPath target t,produced choose read j (secondLoss choose mask Y j) t U z := by
  induction t generalizing U V with
  | nil=>simp [labels_nil] at hmem
  | node i l r hl hr=>
    rcases ht with ⟨htl,htr,hli,hri,hd⟩
    by_cases hi : i=target
    · rw [arrive,ite_eq_left hi] at hv
      have hUV : U=V := Option.some.inj hv
      rw [rightPath,ite_eq_left hi,hUV,sum_empty,add_zero]
    · by_cases hR : target∈labels r
      · have hL : target∉labels l := disjoint_right.mp hd hR
        rw [arrive,ite_eq_right hi] at hv
        cases hc : choose i (z i) U with
        | none=>simp only [hc] at hv; contradiction
        | some c=>
          rw [hc] at hv
          dsimp only at hv
          rw [arrive_absent choose read z target l _ hL] at hv
          have hv' : arrive choose read z target r (U.1,(read i (z i) U c).2)=some V := hv
          have hchild:=hr _ _ htr hR hv'
          rw [rightPath,ite_eq_right hi,ite_eq_left hR]
          have hnot : i∉rightPath target r := fun hj=>hri (rightPath_subset target r hj)
          rw [sum_insert hnot,produced_root]
          have he : (∑ j∈rightPath target r,produced choose read j (secondLoss choose mask Y j)
              (.node i l r) U z)=
              ∑ j∈rightPath target r,produced choose read j (secondLoss choose mask Y j)
                r (U.1,(read i (z i) U c).2) z := by
            apply sum_congr rfl
            intro j hj
            exact produced_right choose read z i j _ l r U (rightPath_subset target r hj) hri hd c hc
          rw [he]
          have hs:=sdiff_inter_card Y U.2 (mask i (z i) U c).2
          have hs' : ((Y\(read i (z i) U c).2).card:ℝ)≤
              ((Y\U.2).card:ℝ)+(Y\(mask i (z i) U c).2).card := by
            rw [hread]
            exact hs
          simp only [secondLoss,hc]
          linarith
      · have hL : target∈labels l := by
          rw [labels_node,mem_insert,mem_union] at hmem
          rcases hmem with he|he|he
          · exact False.elim (hi he.symm)
          · exact he
          · exact False.elim (hR he)
        rw [arrive,ite_eq_right hi] at hv
        cases hc : choose i (z i) U with
        | none=>simp only [hc] at hv; contradiction
        | some c=>
          rw [hc] at hv
          dsimp only at hv
          rw [arrive_absent choose read z target r _ hR] at hv
          have hv' : arrive choose read z target l ((read i (z i) U c).1,U.2)=some V := by
            cases hh : arrive choose read z target l ((read i (z i) U c).1,U.2) with
            | none=>simp [hh] at hv
            | some W=>rw [hh] at hv; exact hv
          have hchild:=hl _ _ htl hL hv'
          rw [rightPath,ite_eq_right hi,ite_eq_right hR]
          have he : (∑ j∈rightPath target l,produced choose read j (secondLoss choose mask Y j)
              (.node i l r) U z)=
              ∑ j∈rightPath target l,produced choose read j (secondLoss choose mask Y j)
                l ((read i (z i) U c).1,U.2) z := by
            apply sum_congr rfl
            intro j hj
            exact produced_left choose read z i j _ l r U (rightPath_subset target l hj) hli hd c hc
          rw [he]
          exact hchild

variable [Fintype I] [∀ i,Fintype (α i)]
theorem expected_second_path_loss (p : ∀ i,Law (α i)) (dummy : ∀ i,α i)
    (choose : ∀ i,α i→Domains A B→Option C)
    (read mask : ∀ i,α i→CapReader A B C) (Y : Finset B)
    (target : I) (t : BinaryTree I) (U : Domains A B)
    (δ : ℝ) (hδ : 0≤δ)
    (hlocal : ∀ i∈rightPath target t,∀ V,
      (∑ x,(p i).mass x*secondLoss choose mask Y i V x)≤δ) :
    (∑ z,(piLaw p).mass z*(∑ j∈rightPath target t,
      produced choose read j (secondLoss choose mask Y j) t U z))≤(t.height:ℝ)*δ := by
  simp_rw [mul_sum]
  rw [sum_comm]
  calc
    _ ≤ ∑ j∈rightPath target t,δ := by
      apply sum_le_sum
      intro j hj
      exact produced_bound p choose read j (dummy j) (secondLoss choose mask Y j) t U δ hδ (hlocal j hj)
    _ = ((rightPath target t).card:ℝ)*δ := by simp only [sum_const,nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast rightPath_card target t) hδ

def secondTrim (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (Y : Finset B)
    (target : I) (t : BinaryTree I) (U : Domains A B) (z : ∀ i,α i) : Prop :=
  ∃ V,arrive choose read z target t U=some V ∧
    ((Y∩V.2).card:ℝ)<(9/10:ℝ)*Y.card

omit [Fintype I] [∀ i,Fintype (α i)] in
theorem reached_second_trim_charge (choose : ∀ i,α i→Domains A B→Option C)
    (read mask : ∀ i,α i→CapReader A B C)
    (hread : ∀ i x U c,(read i x U c).2=U.2∩(mask i x U c).2)
    (z : ∀ i,α i) (target : I) (Y : Finset B) (hY : Y.Nonempty)
    (t : BinaryTree I) (U : Domains A B) (ht : Separated t)
    (hmem : target∈labels t) (hYU : Y⊆U.2) :
    (if secondTrim choose read Y target t U z then (1:ℝ) else 0)≤
      (10/(Y.card:ℝ))*∑ j∈rightPath target t,
        produced choose read j (secondLoss choose mask Y j) t U z := by
  have hy : 0<(Y.card:ℝ) := by exact_mod_cast card_pos.mpr hY
  split_ifs with htrim
  · obtain ⟨V,hv,hsmall⟩:=htrim
    have hl:=reached_second_loss choose read mask hread z target Y t U V ht hmem hv
    rw [sdiff_eq_empty_iff_subset.mpr hYU,card_empty,Nat.cast_zero,zero_add] at hl
    have hc : ((Y\V.2).card:ℝ)+((Y∩V.2).card:ℝ)=Y.card := by
      exact_mod_cast card_sdiff_add_card_inter Y V.2
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hy).mpr
    nlinarith
  · apply mul_nonneg (div_nonneg (by norm_num) hy.le)
    apply sum_nonneg
    intro j _
    exact produced_nonneg choose read j _ (secondLoss_nonneg choose mask Y j) t U z

theorem expected_second_trim (p : ∀ i,Law (α i)) (dummy : ∀ i,α i)
    (choose : ∀ i,α i→Domains A B→Option C)
    (read mask : ∀ i,α i→CapReader A B C)
    (hread : ∀ i x U c,(read i x U c).2=U.2∩(mask i x U c).2)
    (target : I) (Y : Finset B) (hY : Y.Nonempty)
    (t : BinaryTree I) (U : Domains A B) (ht : Separated t)
    (hmem : target∈labels t) (hYU : Y⊆U.2)
    (δ : ℝ) (hδ : 0≤δ)
    (hlocal : ∀ i∈rightPath target t,∀ V,
      (∑ x,(p i).mass x*secondLoss choose mask Y i V x)≤δ) :
    (∑ z,(piLaw p).mass z*(if secondTrim choose read Y target t U z then (1:ℝ) else 0))≤
      (10/(Y.card:ℝ))*t.height*δ := by
  have hy : 0≤10/(Y.card:ℝ) := div_nonneg (by norm_num) (Nat.cast_nonneg _)
  calc
    _ ≤ ∑ z,(piLaw p).mass z*((10/(Y.card:ℝ))*∑ j∈rightPath target t,
        produced choose read j (secondLoss choose mask Y j) t U z) := by
      apply sum_le_sum
      intro z _
      exact mul_le_mul_of_nonneg_left
        (reached_second_trim_charge choose read mask hread z target Y hY t U ht hmem hYU)
        ((piLaw p).nonneg z)
    _ = (10/(Y.card:ℝ))*(∑ z,(piLaw p).mass z*∑ j∈rightPath target t,
        produced choose read j (secondLoss choose mask Y j) t U z) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro z _
      ring
    _ ≤ (10/(Y.card:ℝ))*((t.height:ℝ)*δ) :=
      mul_le_mul_of_nonneg_left
        (expected_second_path_loss p dummy choose read mask Y target t U δ hδ hlocal) hy
    _ = _ := by ring

end
end SharpLogRamsey.FreshExecution

end

end OAI
