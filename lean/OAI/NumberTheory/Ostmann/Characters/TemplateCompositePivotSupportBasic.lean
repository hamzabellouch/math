import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceSupportPropagation

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
attribute [local instance] Classical.propDecidable

theorem coprime_pivot_of_reversal {A HL HR P s v w : ℤ}
    (hA : A ∣ HL) (hR : IsCoprime A HR) (hv : IsCoprime A v)
    (he : v * HR - w * HL = s * P) : IsCoprime A P := by
  obtain ⟨t, ht⟩ := hA
  have hc := (hv.mul_right hR).add_mul_right_right (-w*t)
  have hh : IsCoprime A (s * P) := by
    convert hc using 1
    rw [← he, ht]
    ring
  exact hh.of_mul_right_right

theorem copied_atom_coprime_opposite_product {k j : ℕ} {x : State k (j+1)}
    (hpair : Pairwise (fun i h => IsCoprime (x i) (x h)))
    (b : Bool) (i : {i : (schedule k j).Slot // (schedule k j).IsCopied j i}) :
    IsCoprime (x (.inl (i,b))) (copiedProduct k j (!b) x) := by
  apply IsCoprime.prod_right
  intro h hh
  apply hpair
  intro he
  have hb : b = !b := congrArg Prod.snd (Sum.inl.inj he)
  cases b <;> contradiction

theorem reconstructedPivot_coprime_copied {k j : ℕ} {x : State k (j+1)}
    {s v w : ℤ} (hpair : Pairwise (fun i h => IsCoprime (x i) (x h)))
    (hint : s ∣ v * copiedProduct k j false x - w * copiedProduct k j true x)
    (b : Bool)
    (hfreq : ∀ i : {i : (schedule k j).Slot // (schedule k j).IsCopied j i},
      IsCoprime (if b then v else w) (x (.inl (i,b))))
    (i : {i : (schedule k j).Slot // (schedule k j).IsCopied j i}) :
    IsCoprime (reconstructedPivot k j x s v w) (x (.inl (i,b))) := by
  have he : v * copiedProduct k j false x - w * copiedProduct k j true x =
      s * reconstructedPivot k j x s v w := (Int.mul_ediv_cancel' hint).symm
  cases b with
  | true =>
    have hA : x (.inl (i,true)) ∣ copiedProduct k j true x :=
      Finset.dvd_prod_of_mem (fun a => x (.inl (a,true))) (Finset.mem_univ i)
    have hf : IsCoprime (x (.inl (i,true))) v := (hfreq i).symm
    exact (coprime_pivot_of_reversal hA
      (copied_atom_coprime_opposite_product hpair true i) hf he).symm
  | false =>
    have hA : x (.inl (i,false)) ∣ copiedProduct k j false x :=
      Finset.dvd_prod_of_mem (fun a => x (.inl (a,false))) (Finset.mem_univ i)
    have hf : IsCoprime (x (.inl (i,false))) w := (hfreq i).symm
    have he' : w * copiedProduct k j true x - v * copiedProduct k j false x =
        (-s) * reconstructedPivot k j x s v w := by
      calc
        _ = -(v * copiedProduct k j false x - w * copiedProduct k j true x) := by ring
        _ = _ := by rw [he]; ring
    exact (coprime_pivot_of_reversal hA
      (copied_atom_coprime_opposite_product hpair false i) hf he').symm

theorem childState_pairwise {k j : ℕ} (hj : j < k) {x : State k (j+1)} {P : ℤ}
    (b : Bool) (hpair : Pairwise (fun i h => IsCoprime (x i) (x h)))
    (hcopied : ∀ i : {i : (schedule k j).Slot // (schedule k j).IsCopied j i},
      IsCoprime P (x (.inl (i,b))))
    (houtside : ∀ i : {i : (schedule k j).Slot // (schedule k j).IsOutside j i},
      IsCoprime P (x (.inr i))) :
    Pairwise (fun i h => IsCoprime (childState k j b x P i) (childState k j b x P h)) := by
  intro i h hne
  by_cases hi : (schedule k j).IsPivot j i
  · rw [childState_pivot k j b x P i hi]
    by_cases hh : (schedule k j).IsPivot j h
    · exact False.elim (hne (congrArg Subtype.val
        ((pivotSlot_unique k j hj ⟨i,hi⟩).trans (pivotSlot_unique k j hj ⟨h,hh⟩).symm)))
    · by_cases hc : (schedule k j).IsCopied j h
      · simpa only [childState,dite_eq_right hh,dite_eq_left hc] using hcopied ⟨h,hc⟩
      · simpa only [childState,dite_eq_right hh,dite_eq_right hc] using houtside ⟨h,hh,hc⟩
  · by_cases hh : (schedule k j).IsPivot j h
    · rw [childState_pivot k j b x P h hh]
      by_cases hc : (schedule k j).IsCopied j i
      · simpa only [childState,dite_eq_right hi,dite_eq_left hc] using (hcopied ⟨i,hc⟩).symm
      · simpa only [childState,dite_eq_right hi,dite_eq_right hc] using (houtside ⟨i,hi,hc⟩).symm
    · by_cases hic : (schedule k j).IsCopied j i <;>
        by_cases hhc : (schedule k j).IsCopied j h
      · simpa only [childState,dite_eq_right hi,dite_eq_right hh,dite_eq_left hic,dite_eq_left hhc] using hpair
          (show (Sum.inl (⟨i,hic⟩,b) : (schedule k (j+1)).Slot) ≠ .inl (⟨h,hhc⟩,b) from
            fun he => hne (congrArg (fun z => z.1.val) (Sum.inl.inj he)))
      · simpa only [childState,dite_eq_right hi,dite_eq_right hh,dite_eq_left hic,dite_eq_right hhc] using hpair
          (show (Sum.inl (⟨i,hic⟩,b) : (schedule k (j+1)).Slot) ≠ .inr ⟨h,hh,hhc⟩ from
            fun he => by cases he)
      · simpa only [childState,dite_eq_right hi,dite_eq_right hh,dite_eq_right hic,dite_eq_left hhc] using hpair
          (show (Sum.inr ⟨i,hi,hic⟩ : (schedule k (j+1)).Slot) ≠ .inl (⟨h,hhc⟩,b) from
            fun he => by cases he)
      · simpa only [childState,dite_eq_right hi,dite_eq_right hh,dite_eq_right hic,dite_eq_right hhc] using hpair
          (show (Sum.inr ⟨i,hi,hic⟩ : (schedule k (j+1)).Slot) ≠ .inr ⟨h,hh,hhc⟩ from
            fun he => hne (congrArg Subtype.val (Sum.inr.inj he)))

end Ostmann.Characters.Template

end

end OAI
