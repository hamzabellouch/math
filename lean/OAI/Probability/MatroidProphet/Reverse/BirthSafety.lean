import OAI.Probability.MatroidProphet.Reverse.PrefixTree
import OAI.Probability.MatroidProphet.Reverse.Squared

namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

noncomputable def reverseDoubleExit (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D S : ℕ → Set α) (G : ℕ → Finset α) (k : ℤ) (h : ℕ) (d : α)
    (C T : Finset α) : ℝ :=
  if d ∈ S h then
    (if d ∉ reverseNominal M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) S k h then 1 else 0) *
    (if d ∉ reverseNominal M hE κ D (transitionHybrid M hE κ k D S G C T) S k h then 1 else 0)
  else 0

lemma reverseDoubleExit_mask_congr (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D S : ℕ → Set α) (G : ℕ → Finset α) (k : ℤ) (h : ℕ) (d : α)
    (C C' T : Finset α)
    (hC : ∀ j < h, ∀ e ∈ G j, e ∈ S j → (e ∈ C ↔ e ∈ C')) :
    reverseDoubleExit M hE κ D S G k h d C T = reverseDoubleExit M hE κ D S G k h d C' T := by
  unfold reverseDoubleExit
  rw [reverseNominal_mask_congr M hE κ D S G k h C C' hC,
    reverseHybrid_mask_congr M hE κ D S G k h C C' T hC]

lemma reverseDoubleExit_expectation (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D S : ℕ → Set α) (G : ℕ → Finset α) (k : ℤ) (h : ℕ) (d : α)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ) :
    bitsExpectation q univ (fun C => bitsExpectation q univ (reverseDoubleExit M hE κ D S G k h d C)) =
      if d ∈ S h then (reverseHazard M hE κ D G q d h k S)^2 else 0 := by
  change bitsExpectation q univ (fun C => bitsExpectation q univ (fun T =>
    reverseDoubleExit M hE κ D S G k h d C T)) = _
  by_cases hd : d ∈ S h
  · simp only [reverseDoubleExit, hd, ite_true]
    rw [reverse_double_exit M hE κ k D S G h hG univ (fun _ _ => subset_univ _) q d,
      reverseHazard_eq]
  · simp only [reverseDoubleExit, hd, ite_false, bitsExpectation_const]

theorem reverseDoubleExit_after_prefix (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (h : ℕ) (d : α)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (closed : ReverseClosed M hE κ D k S) (l : ℤ) :
    bitsExpectation q univ (fun C => bitsExpectation q univ
      (reverseDoubleExit M hE κ D ((reversePrefixTree M hE κ D G h m k S).run C) G l h d C)) =
      bitsExpectation q univ (fun C => if d ∈ (reversePrefixTree M hE κ D G h m k S).run C h then
        (reverseHazard M hE κ D G q d h l ((reversePrefixTree M hE κ D G h m k S).run C))^2 else 0) := by
  let f := fun R C => bitsExpectation q univ (reverseDoubleExit M hE κ D R G l h d C)
  have ht := reversePrefixTree_tower M hE κ D G h hG m k S closed q f (by
    intro R C C' hC
    apply bitsExpectation_congr
    intro T hT
    exact reverseDoubleExit_mask_congr M hE κ D R G l h d C C' T hC)
  apply ht.trans
  apply bitsExpectation_congr
  intro C hC
  exact reverseDoubleExit_expectation M hE κ D _ G l h d hG q

lemma reversePrefixTree_from_univ_path (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (m : ℕ) (C : Finset α)
    {j : ℕ} (hj : j ≤ n) :
    (reversePrefixTree M hE κ D G n m (-1) (fun _ => Set.univ)).run C j =
      nominalPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) j (-(m:ℤ)) := by
  rw [reversePrefixTree_run M hE κ D G n hG m (-1) _ (reverseClosed_univ M hE κ D (-1)) C]
  have hS : ∀ i ≤ n, (fun _ => Set.univ) i =
      nominalPath M hE κ D (fun l => (C : Set α) ∩ (G l : Set α)) i (-1+1) := by
    intro i hi
    exact (nominalPath_nonnegative M hE κ D _ i (by omega)).symm
  simpa only [neg_add_cancel, zero_sub] using reverseFinal_path M hE κ D G n hG m (-1) _ C hS hj

omit [DecidableEq α] in
lemma reverseNominal_actual_state (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D S : ℕ → Set α) (G : ℕ → Finset α) (C : Finset α) (b : ℤ) (h : ℕ)
    (hS : ∀ j ≤ h, S j = nominalPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) j b) :
    reverseNominal M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) S (b-1) h =
      nominalPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) h (b-1) := by
  calc
    _ = reverseNominal M hE κ D (fun i => (C : Set α) ∩ (G i : Set α))
        (fun j => nominalPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) j (b-1+1)) (b-1) h := by
      apply reverseNominal_congr_before
      · intro j hj; rfl
      · intro j hj; simpa only [sub_add_cancel] using hS j (by omega)
    _ = _ := reverseNominal_agrees M hE κ D _ (b-1) h

omit [DecidableEq α] in
lemma hybrid_actual_containment (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D S : ℕ → Set α) (G : ℕ → Finset α) (C T : Finset α) (b : ℤ) (h : ℕ)
    (hS : ∀ j ≤ h, S j = nominalPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) j b)
    (hb : activation h ≤ b-1) :
    densityExpansion M hE κ (D h)
      (guardedPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) h (b-2) ∪
        lowerCompetition M hE κ D (fun i => (C : Set α) ∩ (G i : Set α))
          (fun i => (T : Set α) ∩ (G i : Set α)) b h) ⊆
      reverseNominal M hE κ D (transitionHybrid M hE κ (b-1) D S G C T) S (b-1) h := by
  have heq : reverseNominal M hE κ D (transitionHybrid M hE κ (b-1) D S G C T) S (b-1) h =
      reverseNominal M hE κ D
        (hybridGuards M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) (fun i => (T : Set α) ∩ (G i : Set α)) b)
        (fun j => nominalPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) j b) (b-1) h := by
    apply reverseNominal_congr_before
    · intro j hj
      unfold transitionHybrid hybridGuards
      rw [reverseNominal_actual_state M hE κ D S G C b j (fun i hi => hS i (by omega)), hS j (by omega)]
    · intro j hj; exact hS j (by omega)
  rw [heq]
  exact hybrid_containment M hE κ D _ _ b h hb

noncomputable def safeBirthEvent (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (h : ℕ) (d : α) (b : ℤ)
    (C T : Finset α) : Prop :=
  nominalBirth M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) h d = b ∧
    d ∉ densityExpansion M hE κ (D h)
      (guardedPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) h (b-2) ∪
        lowerCompetition M hE κ D (fun i => (C : Set α) ∩ (G i : Set α))
          (fun i => (T : Set α) ∩ (G i : Set α)) b h)

omit [DecidableEq α] in
lemma doubleExit_le_safeBirth (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D S : ℕ → Set α) (G : ℕ → Finset α) (C T : Finset α) (b : ℤ) (h : ℕ)
    (d : α) (hd : d ∉ M.closure ∅)
    (hS : ∀ j ≤ h, S j = nominalPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) j b)
    (hb : activation h ≤ b-1) :
    reverseDoubleExit M hE κ D S G (b-1) h d C T ≤ if safeBirthEvent M hE κ D G h d b C T then 1 else 0 := by
  unfold reverseDoubleExit
  by_cases hs : d ∈ S h
  · rw [ite_eq_left hs]
    by_cases hn : d ∉ reverseNominal M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) S (b-1) h
    · rw [ite_eq_left hn, one_mul]
      by_cases hh : d ∉ reverseNominal M hE κ D (transitionHybrid M hE κ (b-1) D S G C T) S (b-1) h
      · rw [ite_eq_left hh]
        have hbirth : nominalBirth M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) h d = b := by
          rw [hS h le_rfl, mem_nominal_iff_birth_le M hE κ D _ h d hd b] at hs
          rw [reverseNominal_actual_state M hE κ D S G C b h hS,
            mem_nominal_iff_birth_le M hE κ D _ h d hd (b-1)] at hn
          omega
        have hsafe : safeBirthEvent M hE κ D G h d b C T :=
          ⟨hbirth, fun he => hh (hybrid_actual_containment M hE κ D S G C T b h hS hb he)⟩
        simp only [ite_eq_left hsafe, le_refl]
      · simp only [ite_eq_right hh]
        split_ifs <;> norm_num
    · simp only [ite_eq_right hn, zero_mul]
      split_ifs <;> norm_num
  · simp only [ite_eq_right hs]
    split_ifs <;> norm_num

lemma reverseHazard_state_congr (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D S S' : ℕ → Set α) (G : ℕ → Finset α) (q : α → ℝ) (k : ℤ) (h : ℕ) (d : α)
    (hS : ∀ j < h, S j = S' j) :
    reverseHazard M hE κ D G q d h k S = reverseHazard M hE κ D G q d h k S' := by
  rw [reverseHazard_eq, reverseHazard_eq]
  apply bitsExpectation_congr
  intro C hC
  rw [reverseNominal_congr_before M hE κ D _ _ S S' k h (fun _ _ => rfl) hS]

theorem safeBirth_probability (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (h : ℕ) (d : α) (hd : d ∉ M.closure ∅) (m : ℕ) (hb : activation h + 2 ≤ -(m:ℤ)) :
    bitsExpectation q univ (fun C =>
      if d ∈ nominalPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) h (-(m:ℤ)) then
        (reverseHazard M hE κ D G q d h (-(m:ℤ)-1)
          (fun j => nominalPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) j (-(m:ℤ))))^2 else 0) ≤
    bitsExpectation q univ (fun C => bitsExpectation q univ (fun T =>
      if safeBirthEvent M hE κ D G h d (-(m:ℤ)) C T then 1 else 0)) := by
  let P := reversePrefixTree M hE κ D G h m (-1) (fun _ => Set.univ)
  have hP (C : Finset α) (j : ℕ) (hj : j ≤ h) : P.run C j =
      nominalPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) j (-(m:ℤ)) :=
    reversePrefixTree_from_univ_path M hE κ D G h hG m C hj
  have hid := reverseDoubleExit_after_prefix M hE κ D G h d hG q m (-1) (fun _ => Set.univ)
    (reverseClosed_univ M hE κ D (-1)) (-(m:ℤ)-1)
  have heq : bitsExpectation q univ (fun C =>
      if d ∈ nominalPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) h (-(m:ℤ)) then
        (reverseHazard M hE κ D G q d h (-(m:ℤ)-1)
          (fun j => nominalPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) j (-(m:ℤ))))^2 else 0) =
      bitsExpectation q univ (fun C => if d ∈ P.run C h then
        (reverseHazard M hE κ D G q d h (-(m:ℤ)-1) (P.run C))^2 else 0) := by
    apply bitsExpectation_congr
    intro C hC
    rw [hP C h le_rfl, reverseHazard_state_congr M hE κ D (P.run C) _ G q _ h d
      (fun j hj => hP C j hj.le)]
  rw [heq, ← hid]
  apply bitsExpectation_mono q hq0 hq1
  intro C hC
  apply bitsExpectation_mono q hq0 hq1
  intro T hT
  exact doubleExit_le_safeBirth M hE κ D (P.run C) G C T (-(m:ℤ)) h d hd (hP C) (by omega)

end MatroidProphet

end OAI
