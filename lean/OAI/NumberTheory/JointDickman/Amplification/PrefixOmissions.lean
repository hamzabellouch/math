import OAI.NumberTheory.JointDickman.Amplification.CandidateCountScale

namespace OAI

/-! # Few omissions above the addition prefix

This is the deterministic first step in the weighted multiplicity estimate
of `moments.tex`: total and prefix regularity leave at most 4τℓ omissions
above a prefix containing every added prime.
-/

namespace JointDickman
open Finset Classical

theorem omitted_above_count (A R Q : Finset ℕ) (hadd : R \ A ⊆ Q) :
    (((A \ R) \ Q).card : ℝ) =
      (A.card : ℝ)-R.card-((A ∩ Q).card : ℝ)+(R ∩ Q).card := by
  have hsub : R \ Q ⊆ A \ Q := by
    intro p hp
    obtain ⟨hpR,hpQ⟩ := mem_sdiff.mp hp
    refine mem_sdiff.mpr ⟨?_,hpQ⟩
    by_contra hpA
    exact hpQ (hadd (mem_sdiff.mpr ⟨hpR,hpA⟩))
  have he : (A \ R) \ Q = (A \ Q) \ (R \ Q) := by
    ext p
    simp only [Finset.mem_sdiff]
    tauto
  have h₁ := card_sdiff_add_card_eq_card hsub
  have h₂ := card_sdiff_add_card_inter A Q
  have h₃ := card_sdiff_add_card_inter R Q
  rw [← he] at h₁
  have h₁' : (((A \ R) \ Q).card : ℝ)+(R \ Q).card = (A \ Q).card := by exact_mod_cast h₁
  have h₂' : ((A \ Q).card : ℝ)+(A ∩ Q).card = A.card := by exact_mod_cast h₂
  have h₃' : ((R \ Q).card : ℝ)+(R ∩ Q).card = R.card := by exact_mod_cast h₃
  linarith

theorem primePrefix_mono (B : ℕ) (g : ℝ) {A R : Finset ℕ} (h : A ⊆ R) :
    primePrefix B g A ⊆ primePrefix B g R := by
  unfold primePrefix
  split_ifs
  · exact filter_subset_filter _ h
  · exact h

/-- All additions below one grid point force almost all higher prime
factors to be shared by the two regular coefficients. -/
theorem regular_omissions_above_prefix {B L : ℕ} {τ C : ℝ} {A R : Finset ℕ}
    (hL : 1 ≤ L) (hA : RegularPrimeSet B L τ C A) (hR : RegularPrimeSet B L τ C R)
    {k : ℕ} (hk : k ∈ Icc 1 L)
    (hadd : R \ A ⊆ primePrefix B ((k : ℝ)/L) (R \ A)) :
    (((A \ R) \ primePrefix B ((k : ℝ)/L) (A ∪ R)).card : ℝ) ≤
      4*τ*auxiliaryLogLength B := by
  let Q := primePrefix B ((k : ℝ)/L) (A ∪ R)
  have hAQ : A ∩ Q = primePrefix B ((k : ℝ)/L) A := by
    dsimp [Q]
    rw [← primePrefix_inter,inter_eq_left.mpr subset_union_left]
  have hRQ : R ∩ Q = primePrefix B ((k : ℝ)/L) R := by
    dsimp [Q]
    rw [← primePrefix_inter,inter_eq_left.mpr subset_union_right]
  have haddQ : R \ A ⊆ Q := hadd.trans (primePrefix_mono B _
    (sdiff_subset.trans subset_union_right))
  have hc := omitted_above_count A R Q haddQ
  rw [hAQ,hRQ] at hc
  have ha := hA.total_upper hL
  have hr := hR.total_lower hL
  have hap := (hA.1 k hk).1
  have hrp := (hR.1 k hk).2
  nlinarith

end JointDickman

end OAI
