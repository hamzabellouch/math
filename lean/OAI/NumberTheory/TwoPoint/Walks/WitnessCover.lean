import OAI.NumberTheory.TwoPoint.Bounds.MixedDifference
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

namespace OAI

/-!
# A common hybrid containing a private-prime witness family

The product over all witness tests is expanded only to prove existence.
No cardinality of that powerset is charged in an estimate. An omitted
coordinate annihilates the full mixed difference; a surviving term must
therefore cover every singleton coordinate in one common hybrid.
-/

namespace TwoPointCorrelations

open Finset

variable {ι W A : Type*} [Fintype ι] [DecidableEq ι] [Fintype W] [DecidableEq W]

/-- A test depends only on the listed coordinates of the same configuration. -/
def DependsOn (support : Finset ι) (F : (ι → A) → Bool) : Prop :=
  ∀ x y, (∀ i ∈ support, x i = y i) → F x = F y

noncomputable def witnessIntersection (I : W → (ι → A) → Bool) (S : Finset W)
    (x : ι → A) : ℝ := ∏ w ∈ S, if I w x then 1 else 0

noncomputable def witnessAvoidance (I : W → (ι → A) → Bool) (x : ι → A) : ℝ :=
  ∏ w : W, (1 - if I w x then 1 else 0)

def witnessSupport (support : W → Finset ι) (S : Finset W) : Finset ι :=
  S.biUnion support

omit [DecidableEq W] in
lemma mixedDifference_sum (a : ι → A) (F : W → (ι → A) → ℝ) (x : ι → A) :
    mixedDifference a (fun y => ∑ w : W, F w y) x = ∑ w : W, mixedDifference a (F w) x := by
  unfold mixedDifference
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

lemma mixedDifference_const_mul (a : ι → A) (c : ℝ) (F : (ι → A) → ℝ) (x : ι → A) :
    mixedDifference a (fun y => c * F y) x = c * mixedDifference a F x := by
  unfold mixedDifference
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  ring

/-- If one coordinate is irrelevant, its forced-minus-original difference
cancels exactly, regardless of the values of the other coordinates. -/
lemma mixedDifference_eq_zero_of_ignores (a : ι → A) (F : (ι → A) → ℝ) (x : ι → A)
    (i : ι) (hF : ∀ u v, (∀ j, j ≠ i → u j = v j) → F u = F v) :
    mixedDifference a F x = 0 := by
  have hterm (S : Finset ι) (hiS : i ∉ S) :
      (-1 : ℝ) ^ Sᶜ.card * F (forceCoordinates S a x) +
        (-1 : ℝ) ^ (insert i S)ᶜ.card * F (forceCoordinates (insert i S) a x) = 0 := by
    have hvalues : F (forceCoordinates S a x) = F (forceCoordinates (insert i S) a x) := by
      apply hF
      intro j hji
      simp [forceCoordinates_apply, hji]
    have hcard : Sᶜ.card = (insert i S)ᶜ.card + 1 := by
      rw [← insert_compl_insert hiS, card_insert_of_notMem (by simp)]
    rw [hcard, pow_succ, hvalues]
    ring
  unfold mixedDifference
  have hpowerset : (Finset.univ : Finset ι).powerset = (Finset.univ : Finset (Finset ι)) := by ext; simp
  rw [← hpowerset, ← insert_erase (Finset.mem_univ i),
    Finset.sum_powerset_insert (Finset.notMem_erase i Finset.univ), ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro S hS
  exact hterm S (fun hi => (Finset.mem_erase.mp ((Finset.mem_powerset.mp hS) hi)).1 rfl)

omit [Fintype ι] [DecidableEq ι] in
lemma witnessAvoidance_expansion (I : W → (ι → A) → Bool) (x : ι → A) :
    witnessAvoidance I x =
      ∑ S : Finset W, (-1 : ℝ) ^ S.card * witnessIntersection I S x := by
  unfold witnessAvoidance witnessIntersection
  have h := Finset.prod_sub (fun _ : W => (1 : ℝ)) (fun w => if I w x then 1 else 0) Finset.univ
  simpa using h

omit [Fintype ι] [Fintype W] [DecidableEq W] in
lemma witnessIntersection_ignores (support : W → Finset ι) (I : W → (ι → A) → Bool)
    (hdepends : ∀ w, DependsOn (support w) (I w)) (S : Finset W) (i : ι)
    (hi : i ∉ witnessSupport support S) (x y : ι → A)
    (hxy : ∀ j, j ≠ i → x j = y j) :
    witnessIntersection I S x = witnessIntersection I S y := by
  unfold witnessIntersection
  apply Finset.prod_congr rfl
  intro w hw
  have hIw : I w x = I w y := hdepends w x y (by
    intro j hj
    apply hxy j
    intro hji
    exact hi (Finset.mem_biUnion.mpr ⟨w, hw, hji ▸ hj⟩))
  rw [hIw]

/-- A nonzero full mixed difference of the avoidance event forces a family
covering all singleton coordinates, positive in one common hybrid. -/
theorem mixedDifference_common_cover (support : W → Finset ι) (I : W → (ι → A) → Bool)
    (hdepends : ∀ w, DependsOn (support w) (I w)) (a x : ι → A)
    (hnonzero : mixedDifference a (witnessAvoidance I) x ≠ 0) :
    ∃ S : Finset W, witnessSupport support S = Finset.univ ∧
      ∃ H : Finset ι, ∀ w ∈ S, I w (forceCoordinates H a x) = true := by
  have hexp : mixedDifference a (witnessAvoidance I) x =
      ∑ S : Finset W, (-1 : ℝ) ^ S.card * mixedDifference a (witnessIntersection I S) x := by
    have hf : witnessAvoidance I =
        (fun y => ∑ S : Finset W, (-1 : ℝ) ^ S.card * witnessIntersection I S y) :=
      funext (witnessAvoidance_expansion I)
    rw [hf, mixedDifference_sum]
    simp_rw [mixedDifference_const_mul]
  have hterm : ∃ S : Finset W, mixedDifference a (witnessIntersection I S) x ≠ 0 := by
    by_contra! hall
    apply hnonzero
    rw [hexp]
    simp only [hall, mul_zero, Finset.sum_const_zero]
  obtain ⟨S, hS⟩ := hterm
  have hcover : witnessSupport support S = Finset.univ := by
    by_contra hc
    have hex : ∃ i, i ∉ witnessSupport support S := by
      by_contra! hn
      exact hc (Finset.eq_univ_of_forall hn)
    obtain ⟨i, hi⟩ := hex
    exact hS (mixedDifference_eq_zero_of_ignores a (witnessIntersection I S) x i
      (witnessIntersection_ignores support I hdepends S i hi))
  obtain ⟨H, hH⟩ := exists_forced_value_ne_zero a (witnessIntersection I S) x hS
  refine ⟨S, hcover, H, ?_⟩
  intro w hw
  by_contra hIw
  have hz : witnessIntersection I S (forceCoordinates H a x) = 0 := by
    unfold witnessIntersection
    apply Finset.prod_eq_zero hw
    simp [Bool.eq_false_iff.mpr hIw]
  exact hH hz

/-- An inclusion-minimal finite cover has a private coordinate in every
member, and bounded support sizes bound its cardinality from below. -/
theorem exists_private_subcover (support : W → Finset ι) (S : Finset W)
    (hS : witnessSupport support S = Finset.univ) (B : ℕ)
    (hB : ∀ w ∈ S, (support w).card ≤ B) :
    ∃ R ⊆ S, witnessSupport support R = Finset.univ ∧
      Fintype.card ι ≤ R.card * B ∧
      ∀ w ∈ R, ∃ i ∈ support w, ∀ v ∈ R, v ≠ w → i ∉ support v := by
  classical
  have hex : ∃ n : ℕ, ∃ R ⊆ S, witnessSupport support R = Finset.univ ∧ R.card = n :=
    ⟨S.card, S, Finset.Subset.refl S, hS, rfl⟩
  obtain ⟨R, hRS, hcover, hcard⟩ := Nat.find_spec hex
  have hminimal (R' : Finset W) (hR' : R' ⊆ S) (hc : witnessSupport support R' = Finset.univ) :
      R.card ≤ R'.card := by
    have h := Nat.find_min' hex ⟨R', hR', hc, rfl⟩
    omega
  refine ⟨R, hRS, hcover, ?_, ?_⟩
  · calc
      Fintype.card ι = (witnessSupport support R).card := by rw [hcover, Finset.card_univ]
      _ ≤ ∑ w ∈ R, (support w).card := Finset.card_biUnion_le
      _ ≤ ∑ _w ∈ R, B := Finset.sum_le_sum (fun w hw => hB w (hRS hw))
      _ = R.card * B := by simp
  · intro w hw
    by_contra hn
    push Not at hn
    have hdeleted : witnessSupport support (R.erase w) = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro i
      have hi : i ∈ witnessSupport support R := by rw [hcover]; exact Finset.mem_univ _
      obtain ⟨v, hv, hiv⟩ := Finset.mem_biUnion.mp hi
      by_cases hvw : v = w
      · subst v
        obtain ⟨v, hvR, hvw, hiv⟩ := hn i hiv
        exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_erase.mpr ⟨hvw, hvR⟩, hiv⟩
      · exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_erase.mpr ⟨hvw, hv⟩, hiv⟩
    have hmin := hminimal (R.erase w) (Finset.erase_subset _ _ |>.trans hRS) hdeleted
    have hlt := Finset.card_erase_lt_of_mem hw
    omega

/-- Finite-parameter witness cover: enough singleton coordinates compared
with the maximum witness support yields `T` simultaneous witnesses with
pairwise distinct private marked coordinates. -/
theorem mixedDifference_private_witnesses (support : W → Finset ι) (I : W → (ι → A) → Bool)
    (hdepends : ∀ w, DependsOn (support w) (I w)) (a x : ι → A)
    (hnonzero : mixedDifference a (witnessAvoidance I) x ≠ 0)
    (B T : ℕ) (hB : ∀ w, (support w).card ≤ B) (hT : T * B < Fintype.card ι) :
    ∃ R : Finset W, R.card = T ∧ ∃ H : Finset ι,
      (∀ w ∈ R, I w (forceCoordinates H a x) = true) ∧
      ∃ mark : R → ι, Function.Injective mark ∧
        ∀ w : R, mark w ∈ support w ∧ ∀ v ∈ R, v ≠ w → mark w ∉ support v := by
  classical
  obtain ⟨S, hS, H, hH⟩ := mixedDifference_common_cover support I hdepends a x hnonzero
  obtain ⟨Q, hQS, hcover, hcount, hprivate⟩ := exists_private_subcover support S hS B
    (fun w _ => hB w)
  have hTQ : T ≤ Q.card := by nlinarith
  obtain ⟨R, hRQ, hRcard⟩ := Finset.exists_subset_card_eq hTQ
  have hp (w : R) : ∃ i ∈ support w, ∀ v ∈ R, v ≠ w → i ∉ support v := by
    obtain ⟨i, hi, hnot⟩ := hprivate w (hRQ w.property)
    exact ⟨i, hi, fun v hv hne => hnot v (hRQ hv) hne⟩
  choose mark hmark using hp
  refine ⟨R, hRcard, H, (fun w hw => hH w (hQS (hRQ hw))), mark, ?_, hmark⟩
  intro u v huv
  by_contra hne
  have hmem : mark u ∈ support v := by rw [huv]; exact (hmark v).1
  exact (hmark u).2 v v.property (fun heq => hne (Subtype.ext heq.symm)) hmem

end TwoPointCorrelations

end OAI
