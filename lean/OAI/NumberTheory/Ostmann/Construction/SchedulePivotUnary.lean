import OAI.NumberTheory.Ostmann.Construction.ScheduleWordUnary

namespace OAI

/-! # The actual unary on every still-active pivot constituent -/

namespace Ostmann

open scoped Classical

@[simp] theorem copyScheduleOrigin_positive {I : Type*} (n : ℕ) (i : I) :
    copyScheduleOrigin n (copySchedulePositive n i) = i := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

/-- Positive future-pivot copies retain the original multiplier. -/
theorem copyScheduleUnary_pivot {I : Type*} (role : I → CopyScheduleRole)
    (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p) (κ : I → ℕ → ℂ)
    (pivot : ℕ → I) (hpivot : ∀ k, role (pivot k) = .pivot k)
    (i : I) (k : ℕ) (hi : role i = .pivot k) (p : ℕ) [Fact p.Prime]
    (n : ℕ) (hn : n ≤ k) (t : FrequencyTree ℤ n)
    (hfreq : ∀ s ∈ allFrequencyList n t, (s : ZMod p) ≠ 0) :
    copyScheduleUnary χ initialCompleteGraph pivot (initialRegularUnary χ κ) n t
        (copySchedulePositive n i) p =
      regularUnary (χ i p) (κ i p) 1 ((frequencyRoot n t : ℤ) : ZMod p) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hfreqL : ∀ s ∈ allFrequencyList n t.2.1, (s : ZMod p) ≠ 0 := by
      intro s hs
      exact hfreq s (List.mem_cons_of_mem _ (List.mem_append_left _ hs))
    have hg : copyScheduleGraph initialCompleteGraph pivot n (copySchedulePositive n i)
        (copySchedulePositive n (pivot n)) = 1 := by
      apply scheduledRegularRow_pivot role pivot hpivot i k hi n (by omega)
      · exact copyScheduleSurvives_positive role (pivot n) n (hpivot n) n le_rfl
      · intro he
        have hr := congrArg (copyScheduleRole role n) he
        rw [copyScheduleRole_positive role (pivot n) n (hpivot n),
          copyScheduleRole_positive role i k hi] at hr
        have := CopyScheduleRole.pivot.inj hr
        omega
    change copyScheduleUnary χ initialCompleteGraph pivot (initialRegularUnary χ κ) n t.2.1
        (copySchedulePositive n i) p *
      χ (copyScheduleOrigin n (copySchedulePositive n i)) p
        (((frequencyRoot n t.2.1 : ℤ) : ZMod p) * (t.1 : ZMod p)⁻¹) ^
        copyScheduleGraph initialCompleteGraph pivot n (copySchedulePositive n i)
          (copySchedulePositive n (pivot n)) = _
    rw [ih (by omega) t.2.1 hfreqL, copyScheduleOrigin_positive, hg]
    simpa only [regularCopiedMultiplier, ite_true, transferCopySign, one_mul,
      div_eq_mul_inv, frequencyRoot] using
      regularUnary_left (χ i p) (κ i p) 1
        ((frequencyRoot n t.2.1 : ℤ) : ZMod p) (t.1 : ZMod p)
        (hfreqL _ (frequencyRoot_mem_allFrequencyList n t.2.1))

end Ostmann

end OAI
