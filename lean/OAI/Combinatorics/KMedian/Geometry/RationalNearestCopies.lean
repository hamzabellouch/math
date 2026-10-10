import Mathlib

namespace OAI


                                             
section
namespace MetricKMedian.Preparation.RationalNearest
open Finset
variable {α : Type} [LinearOrder α]

def least (U : Finset α) (d : α → ℚ) (hU : U.Nonempty) : α :=
  let m := (U.image d).min' (hU.image _)
  let V := U.filter (fun a => d a=m)
  have hV : V.Nonempty := by
    obtain ⟨a,ha,he⟩ := mem_image.mp (min'_mem (U.image d) (hU.image _))
    exact ⟨a,mem_filter.mpr ⟨ha,he⟩⟩
  V.min' hV

theorem least_spec (U : Finset α) (d : α → ℚ) (hU : U.Nonempty) :
    least U d hU ∈ U ∧ ∀ a∈U, d (least U d hU) ≤ d a := by
  let V := U.filter (fun a => d a=(U.image d).min' (hU.image _))
  have hV : V.Nonempty := by
    obtain ⟨a,ha,he⟩ := mem_image.mp (min'_mem (U.image d) (hU.image _))
    exact ⟨a,mem_filter.mpr ⟨ha,he⟩⟩
  change V.min' hV ∈ U ∧ ∀ a∈U, d (V.min' hV) ≤ d a
  have hh := mem_filter.mp (min'_mem V hV)
  refine ⟨hh.1,fun a ha => ?_⟩
  rw [hh.2]
  exact min'_le _ _ (mem_image.mpr ⟨a,ha,rfl⟩)

def takeNearest (d : α → ℚ) : ℕ → Finset α → Finset α
  | 0,_ => ∅
  | k+1,U => if hU : U.Nonempty then
      insert (least U d hU) (takeNearest d k (U.erase (least U d hU))) else ∅

theorem takeNearest_spec (d : α → ℚ) (k : ℕ) (U : Finset α) (hk : k ≤ U.card) :
    takeNearest d k U ⊆ U ∧ (takeNearest d k U).card=k ∧
    ∀ S : Finset α, S ⊆ U → S.card=k → (∑ a∈takeNearest d k U,d a) ≤ ∑ a∈S,d a := by
  induction k generalizing U with
  | zero =>
    simp only [takeNearest,empty_subset,card_empty,true_and,sum_empty]
    intro S _ hS
    simp [card_eq_zero.mp hS]
  | succ k ih =>
    have hU : U.Nonempty := card_pos.mp (by omega)
    let a := least U d hU
    have ha : a∈U := (least_spec U d hU).1
    have hamin : ∀ b∈U, d a ≤ d b := (least_spec U d hU).2
    have hk' : k ≤ (U.erase a).card := by rw [card_erase_of_mem ha]; omega
    obtain ⟨hsub,hcard,hmin⟩ := ih (U.erase a) hk'
    have han : a∉takeNearest d k (U.erase a) := fun h => (mem_erase.mp (hsub h)).1 rfl
    simp only [takeNearest,dite_eq_left hU]
    change insert a (takeNearest d k (U.erase a)) ⊆ U ∧ _
    refine ⟨insert_subset ha (hsub.trans (erase_subset _ _)),?_,?_⟩
    · rw [card_insert_of_notMem han,hcard]
    · intro S hSU hSk
      rw [sum_insert han]
      by_cases haS : a∈S
      · have hsubS : S.erase a ⊆ U.erase a := erase_subset_erase a hSU
        have hSc : (S.erase a).card=k := by rw [card_erase_of_mem haS,hSk]; omega
        have hh := hmin _ hsubS hSc
        have he := sum_erase_add S d haS
        linarith only [hh,he]
      · have hS : S.Nonempty := card_pos.mp (by omega)
        obtain ⟨b,hb⟩ := hS
        have hsubS : S.erase b ⊆ U.erase a := by
          intro z hz
          have hzS := mem_of_mem_erase hz
          exact mem_erase.mpr ⟨fun he => haS (he ▸ hzS),hSU hzS⟩
        have hSc : (S.erase b).card=k := by rw [card_erase_of_mem hb,hSk]; omega
        have hh := hmin _ hsubS hSc
        have he := sum_erase_add S d hb
        have hd := hamin b (hSU hb)
        linarith only [hh,he,hd]

end MetricKMedian.Preparation.RationalNearest
end

end OAI
