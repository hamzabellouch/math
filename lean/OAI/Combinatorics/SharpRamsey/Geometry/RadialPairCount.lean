import Mathlib

namespace OAI

section
namespace SharpLogRamsey.RadialPairCount
open Finset
open scoped Classical BigOperators
noncomputable section
variable {α ι : Type*}

theorem rich_lines (C : Finset α) (F : Finset ι) (L : ι → Finset α) (r : ℕ)
    (hr : ∀ i ∈ F, r ≤ (C ∩ L i).card)
    (hunique : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → (L i ∩ L j).card ≤ 1) :
    F.card * (r*(r-1)) ≤ C.card^2 := by
  have hd : (↑F : Set ι).PairwiseDisjoint (fun i => (C ∩ L i).offDiag) := by
    intro i hi j hj hij
    apply disjoint_left.mpr
    intro z hzi hzj
    have hi' := mem_offDiag.mp hzi
    have hj' := mem_offDiag.mp hzj
    have htwo : 1 < (L i ∩ L j).card := one_lt_card.mpr
      ⟨z.1, mem_inter.mpr ⟨(mem_inter.mp hi'.1).2,(mem_inter.mp hj'.1).2⟩,
       z.2, mem_inter.mpr ⟨(mem_inter.mp hi'.2.1).2,(mem_inter.mp hj'.2.1).2⟩,hi'.2.2⟩
    exact (not_lt_of_ge (hunique i hi j hj hij)) htwo
  calc
    F.card*(r*(r-1)) = ∑ _i ∈ F, r*(r-1) := by simp
    _ ≤ ∑ i ∈ F, (C ∩ L i).offDiag.card := by
      apply sum_le_sum
      intro i hi
      rw [offDiag_card,← Nat.mul_sub_one]
      exact Nat.mul_le_mul (hr i hi) (Nat.sub_le_sub_right (hr i hi) 1)
    _ = (F.biUnion (fun i => (C ∩ L i).offDiag)).card := (card_biUnion hd).symm
    _ ≤ (C ×ˢ C).card := card_le_card (by
      intro z hz
      obtain ⟨i,hi,hz⟩ := mem_biUnion.mp hz
      have hz' := mem_offDiag.mp hz
      exact mem_product.mpr ⟨(mem_inter.mp hz'.1).1,(mem_inter.mp hz'.2.1).1⟩)
    _ = C.card^2 := by simp [pow_two]

theorem weighted_square_sum (m : ℕ) (c : Fin m → ℕ)
    (hc : Antitone c) :
    (∑ i, (i.val+1)*(c i)^2) ≤ (∑ i, c i)^2 := by
  have hterm (i : Fin m) : (i.val+1)*(c i)^2 ≤
      c i * ∑ j ∈ Finset.univ.filter (fun j : Fin m => j ≤ i), c j := by
    have hcard : (Finset.univ.filter (fun j : Fin m => j ≤ i)).card = i.val+1 := by
      have he : Finset.univ.filter (fun j : Fin m => j ≤ i) = Finset.Iic i := by ext j; simp
      rw [he]
      exact Fin.card_Iic i
    calc
      (i.val+1)*(c i)^2 = (c i)*((Finset.univ.filter (fun j : Fin m => j ≤ i)).card*c i) := by
        rw [hcard]; ring
      _ = c i*(∑ _j ∈ Finset.univ.filter (fun j : Fin m => j ≤ i), c i) := by simp
      _ ≤ _ := by
        apply Nat.mul_le_mul_left
        apply sum_le_sum
        intro j hj
        exact hc (mem_filter.mp hj).2
  calc
    _ ≤ ∑ i, c i * ∑ j ∈ Finset.univ.filter (fun j : Fin m => j ≤ i), c j :=
      sum_le_sum (fun i _ => hterm i)
    _ ≤ ∑ i, c i * ∑ j, c j := by
      apply sum_le_sum
      intro i _
      exact Nat.mul_le_mul_left _ (sum_le_sum_of_subset (filter_subset _ _))
    _ = _ := by rw [← sum_mul]; ring

theorem centered_rich_lines {m : ℕ} (C : Fin m → Finset α)
    (F : Fin m → Finset ι) (L : ι → Finset α) (centers : Fin m → ι → Finset α)
    (r : ℕ) (hr : ∀ i j, j ∈ F i → r ≤ (C i ∩ L j).card)
    (hunique : ∀ i ∈ univ.biUnion F, ∀ j ∈ univ.biUnion F,
      i ≠ j → (L i ∩ L j).card ≤ 1)
    (hcenter : ∀ i j, j ∈ F i → (centers i j).card ≤ i.val)
    (hmono : Antitone (fun i => (C i).card)) :
    ((univ.biUnion (fun i => (F i).biUnion (fun j => centers i j ×ˢ {j}))).card)*
      (r*(r-1)) ≤ (∑ i, (C i).card)^2 := by
  have hcount (i : Fin m) : ((F i).biUnion (fun j => centers i j ×ˢ {j})).card ≤
      i.val*(F i).card := by
    apply (card_biUnion_le).trans
    calc
      (∑ j ∈ F i, (centers i j ×ˢ {j}).card) ≤ ∑ _j ∈ F i, i.val := by
        apply sum_le_sum
        intro j hj
        simpa using hcenter i j hj
      _ = _ := by simp [mul_comm]
  calc
    _ ≤ (∑ i, ((F i).biUnion (fun j => centers i j ×ˢ {j})).card)*(r*(r-1)) :=
      Nat.mul_le_mul_right _ card_biUnion_le
    _ ≤ (∑ i, i.val*(F i).card)*(r*(r-1)) :=
      Nat.mul_le_mul_right _ (sum_le_sum (fun i _ => hcount i))
    _ = ∑ i, i.val*((F i).card*(r*(r-1))) := by
      rw [sum_mul]; apply sum_congr rfl; intros; ring
    _ ≤ ∑ i, (i.val+1)*(C i).card^2 := by
      apply sum_le_sum
      intro i _
      apply Nat.mul_le_mul (by omega)
      apply rich_lines (C i) (F i) L r (hr i)
      intro a ha b hb hab
      exact hunique a (mem_biUnion.mpr ⟨i,mem_univ _,ha⟩)
        b (mem_biUnion.mpr ⟨i,mem_univ _,hb⟩) hab
    _ ≤ _ := weighted_square_sum m (fun i => (C i).card) hmono

end
end SharpLogRamsey.RadialPairCount

end

end OAI
