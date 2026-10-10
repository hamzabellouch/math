import OAI.NumberTheory.Ostmann.Construction.CopyScheduleUnary

namespace OAI

/-! # Frequency-independent multipliers for the actual schedule word slots -/

namespace Ostmann

open scoped ComplexConjugate Classical

noncomputable def initialRegularUnary {I : Type*}
    (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p) (κ : I → ℕ → ℂ)
    (i : I) (v : ℤ) (p : ℕ) : ℂ := regularUnary (χ i p) (κ i p) 1 (v : ZMod p)

/-- All frequency dependence in an actual regular word slot is exactly its
current root character power. The remaining multiplier depends on its copy path. -/
theorem copyScheduleUnary_word {I : Type*} (role : I → CopyScheduleRole)
    (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p) (κ : I → ℕ → ℂ)
    (pivot : ℕ → I) (hpivot : ∀ k, role (pivot k) = .pivot k)
    (i : I) (hi : role i = .word) (p : ℕ) [Fact p.Prime]
    (n : ℕ) (t : FrequencyTree ℤ n) (path : Fin n → Bool)
    (hfreq : ∀ s ∈ allFrequencyList n t, (s : ZMod p) ≠ 0) :
    copyScheduleUnary χ initialCompleteGraph pivot (initialRegularUnary χ κ) n t
        (copySchedulePath n path i) p =
      regularUnary (χ i p) (scheduledWordMultiplier (χ i p) (κ i p) n path)
        (finalCopyParity path) ((frequencyRoot n t : ℤ) : ZMod p) := by
  induction n with
  | zero =>
    simp only [copyScheduleUnary, copySchedulePath, initialRegularUnary, scheduledWordMultiplier,
      finalCopyParity, copyPathParity, frequencyRoot]
  | succ n ih =>
    let path0 : Fin n → Bool := fun j => path j.castSucc
    have hfreqL : ∀ s ∈ allFrequencyList n t.2.1, (s : ZMod p) ≠ 0 := by
      intro s hs
      exact hfreq s (List.mem_cons_of_mem _ (List.mem_append_left _ hs))
    have hfreqR : ∀ s ∈ allFrequencyList n t.2.2, (s : ZMod p) ≠ 0 := by
      intro s hs
      exact hfreq s (List.mem_cons_of_mem _ (List.mem_append_right _ hs))
    have hleft := ih t.2.1 path0 hfreqL
    have hright := ih t.2.2 path0 hfreqR
    have hg : copyScheduleGraph initialCompleteGraph pivot n (copySchedulePath n path0 i)
        (copySchedulePositive n (pivot n)) = finalCopyParity path0 := by
      apply scheduledRegularRow_word role pivot hpivot i hi n path0
      · exact copyScheduleSurvives_positive role (pivot n) n (hpivot n) n le_rfl
      · intro he
        have hr := congrArg (copyScheduleRole role n) he
        rw [copyScheduleRole_positive role (pivot n) n (hpivot n),
          copyScheduleRole_path role i hi] at hr
        cases hr
    have hstep := scheduledWordUnary_step (χ i p) (κ i p) n path0 (path (Fin.last n))
      ((frequencyRoot n t.2.1 : ℤ) : ZMod p) ((frequencyRoot n t.2.2 : ℤ) : ZMod p) (t.1 : ZMod p)
      (hfreqL _ (frequencyRoot_mem_allFrequencyList n t.2.1))
      (hfreqR _ (frequencyRoot_mem_allFrequencyList n t.2.2))
    have hpath : Fin.snoc path0 (path (Fin.last n)) = path := Fin.snoc_init_self path
    rw [hpath] at hstep
    rw [← hpath, copySchedulePath_snoc]
    change copyScheduleUnary χ initialCompleteGraph pivot (initialRegularUnary χ κ) (n + 1) t
      (.inl (path (Fin.last n), copySchedulePath n path0 i)) p = _
    cases hb : path (Fin.last n)
    · rw [show Fin.snoc path0 false = path from by simpa only [hb] using hpath]
      simpa only [copyScheduleUnary, copyScheduleOrigin_path, hg, hright, hb, Bool.false_eq_true,
        ite_false, div_eq_mul_inv, Int.cast_neg, frequencyRoot] using hstep
    · rw [show Fin.snoc path0 true = path from by simpa only [hb] using hpath]
      simpa only [copyScheduleUnary, copyScheduleOrigin_path, hg, hleft, hb, ite_true,
        div_eq_mul_inv, frequencyRoot] using hstep

end Ostmann

end OAI
