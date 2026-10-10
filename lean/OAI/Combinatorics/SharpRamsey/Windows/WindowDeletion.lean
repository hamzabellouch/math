import Mathlib

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset
open scoped Classical BigOperators
noncomputable section
variable {W ι X : Type*} [Fintype W] [Fintype ι] [Fintype X]

def badWindows (e : W×Bool↪ι) (bad : Finset ι) : Finset W :=
  univ.filter (fun i=>e (i,false)∈bad ∨ e (i,true)∈bad)

omit [Fintype ι] in
lemma badWindows_image (e : W×Bool↪ι) (bad : Finset ι) :
    badWindows e bad=(univ.filter (fun z:W×Bool=>e z∈bad)).image Prod.fst := by
  ext i
  simp only [badWindows,mem_filter,mem_univ,true_and,mem_image]
  constructor
  · rintro (h|h)
    · exact ⟨(i,false),h,rfl⟩
    · exact ⟨(i,true),h,rfl⟩
  · rintro ⟨⟨j,b⟩,h,rfl⟩
    cases b
    · exact Or.inl h
    · exact Or.inr h

omit [Fintype ι] in
lemma badWindows_card (e : W×Bool↪ι) (bad : Finset ι) :
    (badWindows e bad).card≤((univ.map e)∩bad).card := by
  rw [badWindows_image]
  have he : (univ.filter (fun z:W×Bool=>e z∈bad)).map e=(univ.map e)∩bad := by
    ext i
    simp only [mem_map,mem_filter,mem_univ,true_and,mem_inter]
    constructor
    · rintro ⟨z,h,rfl⟩
      exact ⟨⟨z,rfl⟩,h⟩
    · rintro ⟨⟨z,rfl⟩,h⟩
      exact ⟨z,h,rfl⟩
  calc
    _ ≤ (univ.filter (fun z:W×Bool=>e z∈bad)).card := card_image_le
    _ = _ := by rw [←he,card_map]

omit [Fintype W] in
theorem downward_sum [LinearOrder W] (S : Finset W) (early late : W→ℝ)
    (lo hi R : ℝ) (hlohi : lo≤hi) (hR : 0≤R)
    (hl : ∀ i∈S,lo≤late i) (hh : ∀ i∈S,early i≤hi)
    (hcross : ∀ i∈S,∀ j∈S,i<j→early j≤late i+R) :
    (∑ i∈S,(early i-late i))≤hi-lo+R*S.card := by
  induction S using Finset.induction_on_min generalizing hi with
  | empty => simpa using sub_nonneg.mpr hlohi
  | @insert i S hmin ih =>
    have hin : i∉S := by intro h; exact (lt_irrefl i) (hmin i h)
    have hli := hl i (mem_insert_self _ _)
    have hhi := hh i (mem_insert_self _ _)
    have hs := ih (late i+R) (by linarith)
      (fun j hj=>hl j (mem_insert_of_mem hj))
      (fun j hj=>hcross i (mem_insert_self _ _) j (mem_insert_of_mem hj) (hmin j hj))
      (fun j hj k hk h=>hcross j (mem_insert_of_mem hj) k (mem_insert_of_mem hk) h)
    rw [sum_insert hin,card_insert_of_notMem hin,Nat.cast_add,Nat.cast_one]
    linarith

theorem downward_deleted [LinearOrder W] (S : Finset W) (early late : W→ℝ)
    (lo hi R D : ℝ) (hlohi : lo≤hi) (hR : 0≤R)
    (hl : ∀ i∈S,lo≤late i) (hh : ∀ i∈S,early i≤hi)
    (hcross : ∀ i∈S,∀ j∈S,i<j→early j≤late i+R) :
    D*((S.filter (fun i=>D<early i-late i)).card:ℝ)≤hi-lo+R*(Fintype.card W:ℝ) := by
  let T:=S.filter (fun i=>D<early i-late i)
  have hlow : D*(T.card:ℝ)≤∑ i∈T,(early i-late i) := by
    calc
      _ = ∑ _i∈T,D := by simp [mul_comm]
      _ ≤ _ := sum_le_sum (fun i hi=>(mem_filter.mp hi).2.le)
  have hsum:=downward_sum T early late lo hi R hlohi hR
    (fun i hi=>hl i (mem_filter.mp hi).1) (fun i hi=>hh i (mem_filter.mp hi).1)
    (fun i hi j hj hij=>hcross i (mem_filter.mp hi).1 j (mem_filter.mp hj).1 hij)
  have hc : (T.card:ℝ) ≤ (Fintype.card W:ℝ) := by exact_mod_cast card_le_univ T
  exact hlow.trans (hsum.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left hc hR)))

def goodTargets (target : W×X↪ι) (keep : Finset W) (bad : Finset ι) : Finset ι :=
  ((keep×ˢ(univ:Finset X)).map target)\bad

omit [Fintype W] [Fintype ι] in
lemma goodTargets_card (target : W×X↪ι) (keep : Finset W) (bad : Finset ι) :
    (keep.card*Fintype.card X)≤(goodTargets target keep bad).card+bad.card := by
  have hsub : ((keep×ˢ(univ:Finset X)).map target) ⊆
      goodTargets target keep bad ∪ bad := by
    intro i hi
    by_cases hb : i∈bad
    · exact mem_union_right _ hb
    · exact mem_union_left _ (mem_sdiff.mpr ⟨hi,hb⟩)
  have h:=card_le_card hsub
  have hh : ((keep×ˢ(univ:Finset X)).map target).card≤
      (goodTargets target keep bad).card+bad.card := by
    simpa only [goodTargets,add_comm] using h.trans (card_union_le _ _)
  simpa only [card_map,card_product,card_univ] using hh

omit [Fintype ι] in
lemma goodTargets_loss (target : W×X↪ι) (lost : Finset W) (bad : Finset ι) :
    Fintype.card W*Fintype.card X≤
      (goodTargets target (univ\lost) bad).card+bad.card+lost.card*Fintype.card X := by
  have h:=goodTargets_card target (univ\lost) bad
  have hc : (univ\lost).card+lost.card=Fintype.card W := by
    simpa using card_sdiff_add_card_eq_card (subset_univ lost)
  nlinarith

end
end SharpLogRamsey.Selection.Windows

end

end OAI
