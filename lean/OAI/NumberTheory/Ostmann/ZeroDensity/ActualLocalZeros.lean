import OAI.NumberTheory.Ostmann.ZeroDensity.ActualPageUniqueness

namespace OAI

/-! # Canonical local exceptional zeros

An actual near-one zero is selected when one exists. Its uniqueness and
completeness follow from the proved Page theorem, not an analytic input.
-/

namespace Ostmann

noncomputable def actualPageConstant : ℝ := Classical.choose exists_actual_page_uniqueness

theorem actualPageConstant_pos : 0 < actualPageConstant :=
  (Classical.choose_spec exists_actual_page_uniqueness).1

theorem actualPage_unique (Q : ℕ) (hQ : 2 ≤ Q) (e f : PrimitiveRealZero)
    (he : e.modulus ≤ Q) (hf : f.modulus ≤ Q)
    (hbe : 1 - actualPageConstant / Real.log (4 * (Q : ℝ)) ≤ e.beta)
    (hbf : 1 - actualPageConstant / Real.log (4 * (Q : ℝ)) ≤ f.beta) : e = f :=
  (Classical.choose_spec exists_actual_page_uniqueness).2 Q hQ e f he hf hbe hbf

noncomputable def actualLocalZero (q : ℕ) : Option PrimitiveRealZero := by
  classical
  exact if h : ∃ e : PrimitiveRealZero, e.modulus ∣ q ∧
      1 - actualPageConstant / Real.log (4 * (q : ℝ)) ≤ e.beta then
    some (Classical.choose h) else none

theorem actualLocalZero_spec (q : ℕ) (e : PrimitiveRealZero)
    (he : actualLocalZero q = some e) :
    e.modulus ∣ q ∧ 1 - actualPageConstant / Real.log (4 * (q : ℝ)) ≤ e.beta := by
  classical
  unfold actualLocalZero at he
  split at he
  next h =>
    have hh := Classical.choose_spec h
    have heq : Classical.choose h = e := Option.some.inj he
    rwa [heq] at hh
  next => simp at he

theorem actualLocalZero_complete (q : ℕ) (hq : 1 ≤ q) (e : PrimitiveRealZero)
    (he : e.modulus ∣ q)
    (hbe : 1 - actualPageConstant / Real.log (4 * (q : ℝ)) ≤ e.beta) :
    actualLocalZero q = some e := by
  classical
  have hq2 : 2 ≤ q := by
    by_contra hn
    have hq1 : q = 1 := by omega
    have he1 : e.modulus = 1 := Nat.eq_one_of_dvd_one (hq1 ▸ he)
    exact e.modulus_ne_one he1
  unfold actualLocalZero
  rw [dite_eq_left ⟨e, he, hbe⟩]
  apply congrArg some
  have hh := Classical.choose_spec (show ∃ f : PrimitiveRealZero, f.modulus ∣ q ∧
      1 - actualPageConstant / Real.log (4 * (q : ℝ)) ≤ f.beta from ⟨e, he, hbe⟩)
  exact actualPage_unique q hq2 _ e (Nat.le_of_dvd (by omega) hh.1)
    (Nat.le_of_dvd (by omega) he) hh.2 hbe

end Ostmann

end OAI
