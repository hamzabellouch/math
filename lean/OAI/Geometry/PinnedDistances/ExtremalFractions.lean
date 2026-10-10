import OAI.Geometry.PinnedDistances.GlobalOverlap

namespace OAI

section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory
noncomputable section
open Filter
open scoped Topology

namespace WeakPinned
open Filter
open scoped Topology

lemma richPairs_subset_offDiag (P : Finset Plane) (s : ℝ) : richPairs P s ⊆ P.offDiag := by
  intro xy h
  obtain ⟨hP,hh,_⟩ := Finset.mem_filter.mp h
  exact Finset.mem_offDiag.mpr ⟨(Finset.mem_product.mp hP).1,(Finset.mem_product.mp hP).2,hh⟩

lemma richPairs_card_le (P : Finset Plane) (s : ℝ) : (richPairs P s).card ≤ P.card*(P.card-1) := by
  calc
    _ ≤ P.offDiag.card := Finset.card_le_card (richPairs_subset_offDiag P s)
    _ = _ := by rw [Finset.offDiag_card,Nat.mul_sub_one]

lemma pairFraction_nonneg (P : Finset Plane) (s : ℝ) : 0 ≤ pairFraction P s := by
  by_cases hn : 1 ≤ P.card
  · exact div_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (by exact_mod_cast hn)))
  · have hz : P.card=0 := by omega
    simp [pairFraction,hz]

lemma pairFraction_le_one (P : Finset Plane) (s : ℝ) : pairFraction P s ≤ 1 := by
  by_cases hn : 2 ≤ P.card
  · have hd : 0 < (P.card : ℝ)*((P.card : ℝ)-1) := by
      have : (2:ℝ) ≤ P.card := by exact_mod_cast hn
      nlinarith
    rw [pairFraction,div_le_one hd]
    have hh := richPairs_card_le P s
    have h1 : 1 ≤ P.card := by omega
    exact_mod_cast (show (richPairs P s).card ≤ P.card*(P.card-1) from hh)
  · have hc : P.card=0 ∨ P.card=1 := by omega
    rcases hc with hc | hc <;> simp [pairFraction,hc]

lemma fraction_values_nonempty (n : ℕ) (s : ℝ) :
    ({a : ℝ | ∃ P : Finset Plane, P.card=n ∧ a=pairFraction P s}).Nonempty := by
  obtain ⟨P,hP⟩ := Finset.exists_card_eq (α:=Plane) n
  exact ⟨_,P,hP,rfl⟩

lemma fraction_values_bddAbove (n : ℕ) (s : ℝ) :
    BddAbove {a : ℝ | ∃ P : Finset Plane, P.card=n ∧ a=pairFraction P s} := by
  refine ⟨1,?_⟩
  rintro a ⟨P,_,rfl⟩
  exact pairFraction_le_one P s

lemma fraction_le_F (P : Finset Plane) (s : ℝ) (hn : 2 ≤ P.card) : pairFraction P s ≤ F P.card s := by
  rw [F,ite_eq_left hn]
  exact le_csSup (fraction_values_bddAbove _ _) ⟨P,rfl,rfl⟩

lemma F_nonneg (n : ℕ) (s : ℝ) : 0 ≤ F n s := by
  by_cases hn : 2 ≤ n
  · obtain ⟨P,hP⟩ := Finset.exists_card_eq (α:=Plane) n
    rw [← hP] at hn ⊢
    exact (pairFraction_nonneg P s).trans (fraction_le_F P s hn)
  · simp [F,hn]

lemma F_le_one (n : ℕ) (s : ℝ) : F n s ≤ 1 := by
  unfold F
  split_ifs
  · exact csSup_le (fraction_values_nonempty _ _) (by rintro a ⟨P,_,rfl⟩; exact pairFraction_le_one P s)
  · norm_num

lemma F_attained (n : ℕ) (hn : 2 ≤ n) (s : ℝ) :
    ∃ P : Finset Plane, P.card=n ∧ F n s=pairFraction P s := by
  classical
  let A : Finset ℕ := (Finset.range (n*(n-1)+1)).filter (fun k => ∃ P : Finset Plane, P.card=n ∧ (richPairs P s).card=k)
  obtain ⟨P,hP⟩ := Finset.exists_card_eq (α:=Plane) n
  have hA : (richPairs P s).card ∈ A := by
    simp only [A,Finset.mem_filter,Finset.mem_range]
    refine ⟨?_,P,hP,rfl⟩
    have hh := richPairs_card_le P s
    rw [hP] at hh
    omega
  obtain ⟨k,hk,hmax⟩ := Finset.exists_max_image A id ⟨_,hA⟩
  obtain ⟨Q,hQ,hkQ⟩ := (Finset.mem_filter.mp hk).2
  refine ⟨Q,hQ,le_antisymm ?_ ?_⟩
  · rw [F,ite_eq_left hn]
    apply csSup_le (fraction_values_nonempty _ _)
    rintro a ⟨R,hR,rfl⟩
    have hm : (richPairs R s).card ∈ A := by
      simp only [A,Finset.mem_filter,Finset.mem_range]
      refine ⟨?_,R,hR,rfl⟩
      have hh := richPairs_card_le R s
      rw [hR] at hh
      omega
    have hh := hmax _ hm
    change (richPairs R s).card ≤ k at hh
    simp only [pairFraction,hR,hQ]
    exact div_le_div_of_nonneg_right (by exact_mod_cast (hkQ ▸ hh)) (by
      have : (2:ℝ) ≤ n := by exact_mod_cast hn
      nlinarith)
  · rw [← hQ]
    exact fraction_le_F Q s (hQ ▸ hn)

lemma k_lt_card {P : Finset Plane} {x y : Plane} (hx : x ∈ P) : k P x y < P.card := by
  calc
    _ ≤ (P.erase x).card := Finset.card_le_card (Finset.filter_subset _ _)
    _ < P.card := Finset.card_erase_lt_of_mem hx

lemma richPairs_antitone {P : Finset Plane} (hn : 1 ≤ P.card) {s t : ℝ} (hst : s ≤ t) :
    richPairs P t ⊆ richPairs P s := by
  intro xy h
  obtain ⟨hP,hne,hk⟩ := Finset.mem_filter.mp h
  apply Finset.mem_filter.mpr
  refine ⟨hP,hne,?_⟩
  exact (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hst).trans hk

lemma fraction_antitone {P : Finset Plane} (hn : 2 ≤ P.card) : Antitone (pairFraction P) := by
  intro s t hst
  unfold pairFraction
  apply div_le_div_of_nonneg_right
  · exact_mod_cast Finset.card_le_card (richPairs_antitone (by omega) hst)
  · have : (2:ℝ) ≤ P.card := by exact_mod_cast hn
    nlinarith

lemma F_antitone (n : ℕ) : Antitone (F n) := by
  intro s t hst
  by_cases hn : 2 ≤ n
  · obtain ⟨P,hP,hF⟩ := F_attained n hn t
    rw [hF]
    have hPn : 2 ≤ P.card := hP ▸ hn
    calc
      _ ≤ pairFraction P s := fraction_antitone hPn hst
      _ ≤ F n s := by simpa [hP] using fraction_le_F P s hPn
  · simp [F,hn]

lemma F_eq_zero_of_one_le (n : ℕ) {s : ℝ} (hs : 1 ≤ s) : F n s=0 := by
  by_cases hn : 2 ≤ n
  · obtain ⟨P,hP,hF⟩ := F_attained n hn s
    have hz : richPairs P s=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro xy hh
      obtain ⟨hxy,_,hk⟩ := Finset.mem_filter.mp hh
      have hlt := k_lt_card (x:=xy.1) (y:=xy.2) (Finset.mem_product.mp hxy).1
      have h1 : (1:ℝ) ≤ P.card := by rw [hP]; exact_mod_cast (show 1 ≤ n by omega)
      have hr := Real.rpow_le_rpow_of_exponent_le h1 hs
      rw [Real.rpow_one] at hr
      have hlt' : (k P xy.1 xy.2 : ℝ) < P.card := by exact_mod_cast hlt
      linarith
    rw [hF,pairFraction,hz]
    simp
  · simp [F,hn]

end WeakPinned

end
end
end
end
end
end
end

end OAI
