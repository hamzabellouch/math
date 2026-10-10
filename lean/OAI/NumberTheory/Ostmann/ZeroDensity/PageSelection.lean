import OAI.NumberTheory.Ostmann.ZeroDensity.PublishedProgressionInputs

namespace OAI

/-! # A single exceptional character for every modulus in a row

Only zeros in Page's common region are retained. Local exceptional zeros
outside that region will be bounded as an error, rather than identified
with a character belonging to a different modulus.
-/

namespace Ostmann

open Classical

noncomputable def selectedPageZero (P : PublishedProgressionInput) (Q : ℕ) :
    Option PrimitiveRealZero :=
  if h : ∃ e : PrimitiveRealZero, e.modulus ≤ Q ∧
      1 - P.kappa / Real.log (4 * (Q : ℝ)) ≤ e.beta then some h.choose else none

noncomputable def pageAtModulus (q : ℕ) (z : Option PrimitiveRealZero) :
    Option PrimitiveRealZero :=
  z.bind fun e => if e.modulus ∣ q then some e else none

theorem selectedPageZero_spec (P : PublishedProgressionInput) (Q : ℕ)
    (e : PrimitiveRealZero) (he : selectedPageZero P Q = some e) :
    e.modulus ≤ Q ∧ 1 - P.kappa / Real.log (4 * (Q : ℝ)) ≤ e.beta := by
  unfold selectedPageZero at he
  split at he
  next hex =>
    have h := Option.some.inj he
    exact h ▸ hex.choose_spec
  next => simp at he

theorem selectedPageZero_eq (P : PublishedProgressionInput) (Q : ℕ)
    (hQ : 2 ≤ Q) (e : PrimitiveRealZero) (hmod : e.modulus ≤ Q)
    (hnear : 1 - P.kappa / Real.log (4 * (Q : ℝ)) ≤ e.beta) :
    selectedPageZero P Q = some e := by
  have hex : ∃ f : PrimitiveRealZero, f.modulus ≤ Q ∧
      1 - P.kappa / Real.log (4 * (Q : ℝ)) ≤ f.beta := ⟨e, hmod, hnear⟩
  have heq := P.unique Q hQ hex.choose e hex.choose_spec.1 hmod hex.choose_spec.2 hnear
  unfold selectedPageZero
  rw [dite_eq_left hex, heq]

theorem page_region_mono (P : PublishedProgressionInput) {q Q : ℕ}
    (hq : 1 ≤ q) (hqQ : q ≤ Q) :
    1 - P.kappa / Real.log (4 * (q : ℝ)) ≤
      1 - P.kappa / Real.log (4 * (Q : ℝ)) := by
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hpos : 0 < Real.log (4 * (q : ℝ)) := Real.log_pos (by linarith)
  have hlog : Real.log (4 * (q : ℝ)) ≤ Real.log (4 * (Q : ℝ)) :=
    Real.log_le_log (by positivity) (by exact_mod_cast Nat.mul_le_mul_left 4 hqQ)
  have hdiv := div_le_div_of_nonneg_left P.kappa_pos.le hpos hlog
  linarith

theorem localZero_eq_of_selected (P : PublishedProgressionInput) {q Q : ℕ}
    (hq : 1 ≤ q) (hqQ : q ≤ Q) (e : PrimitiveRealZero)
    (he : selectedPageZero P Q = some e) (hd : e.modulus ∣ q) :
    P.localZero q = some e :=
  P.complete q hq e hd
    ((page_region_mono P hq hqQ).trans (selectedPageZero_spec P Q e he).2)

/-- Every local correction either equals the restriction of the same global
Page correction, or is a zero lying strictly outside the common region.
In the latter case the global correction is absent from that modulus. -/
theorem localZero_selected_alternative (P : PublishedProgressionInput) {q Q : ℕ}
    (hQ : 2 ≤ Q) (hq : 1 ≤ q) (hqQ : q ≤ Q) :
    P.localZero q = pageAtModulus q (selectedPageZero P Q) ∨
      ∃ e : PrimitiveRealZero, P.localZero q = some e ∧
        e.beta < 1 - P.kappa / Real.log (4 * (Q : ℝ)) ∧
        pageAtModulus q (selectedPageZero P Q) = none := by
  cases hl : P.localZero q with
  | none =>
    left
    cases hg : selectedPageZero P Q with
    | none => simp [pageAtModulus]
    | some e =>
      by_cases hd : e.modulus ∣ q
      · have hc := localZero_eq_of_selected P hq hqQ e hg hd
        rw [hl] at hc
        contradiction
      · simp [pageAtModulus, hd]
  | some e =>
    have hd := P.divides q e hl
    by_cases hn : 1 - P.kappa / Real.log (4 * (Q : ℝ)) ≤ e.beta
    · left
      have he := selectedPageZero_eq P Q hQ e
        ((Nat.le_of_dvd (by omega) hd).trans hqQ) hn
      simp [he, pageAtModulus, hd]
    · right
      refine ⟨e, rfl, lt_of_not_ge hn, ?_⟩
      cases hg : selectedPageZero P Q with
      | none => simp [pageAtModulus]
      | some f =>
        by_cases hf : f.modulus ∣ q
        · have hc := localZero_eq_of_selected P hq hqQ f hg hf
          rw [hl] at hc
          have hef := Option.some.inj hc
          exact False.elim (hn (hef ▸ (selectedPageZero_spec P Q f hg).2))
        · simp [pageAtModulus, hf]

end Ostmann

end OAI
