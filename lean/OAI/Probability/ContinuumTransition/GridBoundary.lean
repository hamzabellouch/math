import OAI.Probability.ContinuumTransition.KacGrid

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

noncomputable def indexInterval (m q : ℕ) : Finset ℤ :=
  Finset.Icc (-(m : ℤ)*(q : ℤ)) ((m : ℤ)*(q : ℤ))

noncomputable def edgeResidues (q H : ℕ) : Finset ℤ :=
  Finset.Ico 0 (H : ℤ) ∪ Finset.Ico ((q : ℤ)-(H : ℤ)) (q : ℤ)

noncomputable def edgeIndices (m q H : ℕ) : Finset ℤ :=
  (indexInterval m q).filter (fun k => k%(q : ℤ) ∈ edgeResidues q H)

theorem card_indexInterval (m q : ℕ) : (indexInterval m q).card = 2*m*q+1 := by
  unfold indexInterval
  rw [Int.card_Icc]
  have he : (m : ℤ)*(q : ℤ)+1-(-(m : ℤ)*(q : ℤ)) = ((2*m*q+1 : ℕ) : ℤ) := by push_cast; ring
  rw [he, Int.toNat_natCast]

theorem card_edgeResidues_le (q H : ℕ) : (edgeResidues q H).card ≤ 2*H := by
  have hh := Finset.card_union_le (Finset.Ico (0 : ℤ) (H : ℤ))
    (Finset.Ico ((q : ℤ)-(H : ℤ)) (q : ℤ))
  rw [Int.card_Ico, Int.card_Ico, sub_zero, sub_sub_cancel, Int.toNat_natCast] at hh
  simpa only [edgeResidues, two_mul] using hh

theorem card_edgeIndices_le (m q H : ℕ) (hq : 0 < q) :
    (edgeIndices m q H).card ≤ (2*m+1)*(2*H) := by
  let target := (indexInterval m 1) ×ˢ edgeResidues q H
  have hq' : (0 : ℤ) < q := by exact_mod_cast hq
  have hmap (k : ℤ) (hk : k ∈ edgeIndices m q H) : (k/(q : ℤ), k%(q : ℤ)) ∈ target := by
    obtain ⟨hk, he⟩ := Finset.mem_filter.mp hk
    obtain ⟨hkl, hku⟩ := Finset.mem_Icc.mp hk
    have hlo := Int.ediv_le_ediv hq' hkl
    have hhi := Int.ediv_le_ediv hq' hku
    simp only [Int.mul_ediv_cancel _ (ne_of_gt hq')] at hlo hhi
    apply Finset.mem_product.mpr ⟨?_, he⟩
    simpa only [indexInterval, Finset.mem_Icc, Nat.cast_one, mul_one] using And.intro hlo hhi
  have hinj (k l : ℤ) (_ : k ∈ edgeIndices m q H) (_ : l ∈ edgeIndices m q H)
      (he : (k/(q : ℤ), k%(q : ℤ)) = (l/(q : ℤ), l%(q : ℤ))) : k = l := by
    have he1 : k/(q : ℤ) = l/(q : ℤ) := congrArg Prod.fst he
    have he2 : k%(q : ℤ) = l%(q : ℤ) := congrArg Prod.snd he
    have hk := Int.emod_add_mul_ediv k (q : ℤ)
    have hl := Int.emod_add_mul_ediv l (q : ℤ)
    rw [he1, he2] at hk
    exact hk.symm.trans hl
  have hc := Finset.card_le_card_of_injOn (fun k : ℤ => (k/(q : ℤ), k%(q : ℤ))) hmap (fun k hk l hl => hinj k l hk hl)
  calc
    _ ≤ target.card := hc
    _ = (2*m+1)*(edgeResidues q H).card := by rw [Finset.card_product, card_indexInterval]; simp
    _ ≤ _ := Nat.mul_le_mul_left _ (card_edgeResidues_le q H)

theorem edgeResidue_of_crossing {q H : ℕ} (hq : 0 < q) {k l : ℤ}
    (hkl : |k-l| ≤ (H : ℤ)) (hcross : k/(q : ℤ) ≠ l/(q : ℤ)) :
    k%(q : ℤ) ∈ edgeResidues q H := by
  by_contra he
  have hq' : (0 : ℤ) < q := by exact_mod_cast hq
  have hk0 := Int.emod_nonneg k (ne_of_gt hq')
  have hkq := Int.emod_lt_of_pos k hq'
  have hl0 := Int.emod_nonneg l (ne_of_gt hq')
  have hlq := Int.emod_lt_of_pos l hq'
  have hlo : (H : ℤ) ≤ k%(q : ℤ) := by
    by_contra! hh
    exact he (Finset.mem_union_left _ (Finset.mem_Ico.mpr ⟨hk0, hh⟩))
  have hhi : k%(q : ℤ) < (q : ℤ)-(H : ℤ) := by
    by_contra! hh
    exact he (Finset.mem_union_right _ (Finset.mem_Ico.mpr ⟨hh, hkq⟩))
  have hk := Int.emod_add_mul_ediv k (q : ℤ)
  have hl := Int.emod_add_mul_ediv l (q : ℤ)
  obtain ⟨hd1, hd2⟩ := abs_le.mp hkl
  rcases lt_or_gt_of_ne hcross with hh | hh
  · have hh' : k/(q : ℤ)+1 ≤ l/(q : ℤ) := by omega
    have hm := mul_nonneg hq'.le (sub_nonneg.mpr hh')
    nlinarith
  · have hh' : l/(q : ℤ)+1 ≤ k/(q : ℤ) := by omega
    have hm := mul_nonneg hq'.le (sub_nonneg.mpr hh')
    nlinarith

end ContinuumTemperature
end

end OAI
