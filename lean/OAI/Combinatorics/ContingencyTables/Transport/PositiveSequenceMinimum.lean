import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

namespace OAI

/-! # Endpoint minimum for a positive finite log-concave sequence

This is the finite inequality needed by the conditional-variance paths.
After one strict decrease, the local product inequality forces every
subsequent step to decrease, so there can be no valley between endpoints.
-/

namespace ContingencyTables

lemma positive_sequence_drop (a : ℕ → ℝ) (N k : ℕ)
    (hpos : ∀ i, i ≤ N → 0 < a i)
    (hlog : ∀ i, i+2 ≤ N → a i*a (i+2) ≤ (a (i+1))^2)
    (hk : k+2 ≤ N) (hdrop : a (k+1)<a k) : a (k+2)<a (k+1) := by
  have h0 := hpos k (by omega)
  have h1 := hpos (k+1) (by omega)
  have h2 := hlog k hk
  by_contra hn
  have hnext : a (k+1) ≤ a (k+2) := le_of_not_gt hn
  have hprod := mul_le_mul_of_nonneg_left hnext h0.le
  have hstrict := mul_lt_mul_of_pos_right hdrop h1
  nlinarith

/-- Only positivity and the local three-term product inequality are
needed, on the finite interval actually used by the application. -/
theorem positive_sequence_minimum (a : ℕ → ℝ) (N i j k : ℕ)
    (hpos : ∀ n, n ≤ N → 0 < a n)
    (hlog : ∀ n, n+2 ≤ N → a n*a (n+2) ≤ (a (n+1))^2)
    (hij : i ≤ j) (hjk : j ≤ k) (hkN : k ≤ N) : min (a i) (a k) ≤ a j := by
  by_cases hleft : a i ≤ a j
  · exact (min_le_left _ _).trans hleft
  · have hex : ∃ r, i ≤ r ∧ r<j ∧ a (r+1)<a r := by
      by_contra hn
      have hstep : ∀ r, i ≤ r → r<j → a r ≤ a (r+1) := by
        intro r hir hrj
        by_contra hr
        exact hn ⟨r,hir,hrj,lt_of_not_ge hr⟩
      have hm : ∀ n, i ≤ n → n ≤ j → a i ≤ a n := by
        intro n hin
        induction n,hin using Nat.le_induction with
        | base => intro _; exact le_rfl
        | succ n hin ih =>
          intro hnj
          exact (ih (by omega)).trans (hstep n hin (by omega))
      exact hleft (hm j hij le_rfl)
    obtain ⟨r,hir,hrj,hdrop⟩ := hex
    have hdecrease : ∀ n, r ≤ n → n+1 ≤ N → a (n+1)<a n := by
      intro n hrn
      induction n,hrn using Nat.le_induction with
      | base => intro _; exact hdrop
      | succ n hrn ih =>
        intro hnN
        exact positive_sequence_drop a N n hpos hlog (by omega) (ih (by omega))
    have hm : ∀ n, j ≤ n → n ≤ k → a n ≤ a j := by
      intro n hjn
      induction n,hjn using Nat.le_induction with
      | base => intro _; exact le_rfl
      | succ n hjn ih =>
        intro hnk
        exact (hdecrease n (by omega) (by omega)).le.trans (ih (by omega))
    exact (min_le_right _ _).trans (hm k hjk le_rfl)

end ContingencyTables

end OAI
