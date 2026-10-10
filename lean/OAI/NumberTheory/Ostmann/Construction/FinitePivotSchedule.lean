import OAI.NumberTheory.Ostmann.Construction.ScheduledArithmeticIteration

namespace OAI

/-! # Finite pivot hypotheses for a finite-depth arithmetic schedule

Only the pivots through the current depth occur in these formulas. The
finite construction therefore supplies exactly those roles, without a
hypothesis requiring infinitely many roles in a finite type.
-/
namespace Ostmann
open scoped Classical BigOperators

theorem scheduledRegularRow_pivot_finite {I : Type*} (role : I → CopyScheduleRole)
    (pivot : ℕ → I) (i : I) (k : ℕ) (hi : role i = .pivot k)
    (n : ℕ) (hn : n ≤ k) (hpivot : ∀ j ≤ n, role (pivot j) = .pivot j) :
    ScheduledRegularRow role initialCompleteGraph pivot n (copySchedulePositive n i) 1 := by
  induction n with
  | zero =>
    intro j _ hji
    exact initialCompleteGraph_of_ne hji.symm
  | succ n ih =>
    have hnk : n < k := by omega
    have hpn := hpivot n (Nat.le_succ n)
    have hc : (copyScheduleRole role n (copySchedulePositive n i)).copiedAt n = true := by
      rw [copyScheduleRole_positive role i k hi]
      simpa [CopyScheduleRole.copiedAt] using hnk
    have hp := copyScheduleSurvives_positive role (pivot n) n hpn n le_rfl
    have hne : copySchedulePositive n (pivot n) ≠ copySchedulePositive n i := by
      intro he
      have h := congrArg (copyScheduleRole role n) he
      rw [copyScheduleRole_positive role (pivot n) n hpn, copyScheduleRole_positive role i k hi] at h
      have : n = k := CopyScheduleRole.pivot.inj h
      omega
    exact scheduledRegularRow_copy role initialCompleteGraph pivot n _ _
      (ih (by omega) (fun j hj => hpivot j (hj.trans (Nat.le_succ n)))) hc hp hne true

theorem copyScheduleUnary_pivot_finite {I : Type*} (role : I → CopyScheduleRole)
    (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p) (κ : I → ℕ → ℂ)
    (pivot : ℕ → I) (i : I) (k : ℕ) (hi : role i = .pivot k) (p : ℕ) [Fact p.Prime]
    (n : ℕ) (hn : n ≤ k) (hpivot : ∀ j ≤ n, role (pivot j) = .pivot j)
    (t : FrequencyTree ℤ n)
    (hfreq : ∀ s ∈ allFrequencyList n t, (s : ZMod p) ≠ 0) :
    copyScheduleUnary χ initialCompleteGraph pivot (initialRegularUnary χ κ) n t
        (copySchedulePositive n i) p =
      regularUnary (χ i p) (κ i p) 1 ((frequencyRoot n t : ℤ) : ZMod p) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hpn := hpivot n (Nat.le_succ n)
    have hpast : ∀ j ≤ n, role (pivot j) = .pivot j :=
      fun j hj => hpivot j (hj.trans (Nat.le_succ n))
    have hfreqL : ∀ s ∈ allFrequencyList n t.2.1, (s : ZMod p) ≠ 0 := by
      intro s hs
      exact hfreq s (List.mem_cons_of_mem _ (List.mem_append_left _ hs))
    have hg : copyScheduleGraph initialCompleteGraph pivot n (copySchedulePositive n i)
        (copySchedulePositive n (pivot n)) = 1 := by
      apply scheduledRegularRow_pivot_finite role pivot i k hi n (by omega) hpast
      · exact copyScheduleSurvives_positive role (pivot n) n hpn n le_rfl
      · intro he
        have hr := congrArg (copyScheduleRole role n) he
        rw [copyScheduleRole_positive role (pivot n) n hpn,
          copyScheduleRole_positive role i k hi] at hr
        have := CopyScheduleRole.pivot.inj hr
        omega
    change copyScheduleUnary χ initialCompleteGraph pivot (initialRegularUnary χ κ) n t.2.1
        (copySchedulePositive n i) p *
      χ (copyScheduleOrigin n (copySchedulePositive n i)) p
        (((frequencyRoot n t.2.1 : ℤ) : ZMod p) * (t.1 : ZMod p)⁻¹) ^
        copyScheduleGraph initialCompleteGraph pivot n (copySchedulePositive n i)
          (copySchedulePositive n (pivot n)) = _
    rw [ih (by omega) hpast t.2.1 hfreqL, copyScheduleOrigin_positive, hg]
    simpa only [regularCopiedMultiplier, ite_true, transferCopySign, one_mul,
      div_eq_mul_inv, frequencyRoot] using
      regularUnary_left (χ i p) (κ i p) 1
        ((frequencyRoot n t.2.1 : ℤ) : ZMod p) (t.1 : ZMod p)
        (hfreqL _ (frequencyRoot_mem_allFrequencyList n t.2.1))

theorem scheduledRetainedGraph_pivot_column_finite {I : Type*} (role : I → CopyScheduleRole)
    (pivot : ℕ → I) (n : ℕ) (hpivot : role (pivot n) = .pivot n)
    (p : I) (hp : role p = .pivot n) (i : CopyScheduleH role n ⊕ CopyScheduleY role n) :
    scheduledRetainedGraph role initialCompleteGraph pivot n (some i) none =
      copyScheduleGraph initialCompleteGraph pivot n
        (Sum.elim Subtype.val Subtype.val i) (copySchedulePositive n p) := by
  cases i with
  | inl i =>
    apply copyScheduleGraph_pivot_common_column role pivot n (pivot n) p hpivot hp n le_rfl i.val i.property.1
    intro he
    have hc := i.property.2
    rw [he] at hc
    simp [CopyScheduleRole.copiedAt] at hc
  | inr i =>
    apply copyScheduleGraph_pivot_common_column role pivot n (pivot n) p hpivot hp n le_rfl i.val i.property.1
    intro he
    have hc := i.property.2.2
    rw [he] at hc
    simp [CopyScheduleRole.erasedAt] at hc

end Ostmann

end OAI
