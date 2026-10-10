import OAI.NumberTheory.Ostmann.Construction.ScheduleWordSlots

namespace OAI

/-! # The active pivot group has exactly its original constituent slots -/

namespace Ostmann

theorem CopyScheduleRole.afterCopy_eq_pivot (r : CopyScheduleRole) (b : Bool) (k : ℕ) :
    r.afterCopy b = .pivot k ↔ b = true ∧ r = .pivot k := by
  cases r <;> cases b <;> simp [afterCopy]

theorem copySchedulePositive_injective {I : Type*} (n : ℕ) :
    Function.Injective (copySchedulePositive (I := I) n) := by
  induction n with
  | zero => exact fun _ _ h => h
  | succ n ih =>
    intro i j h
    exact ih (Prod.mk.inj (Sum.inl.inj h)).2

/-- No old pivot can remain active: the active group is copied positively
until its own step and is then erased in its entirety. -/
theorem surviving_pivot_is_positive {I : Type*} (role : I → CopyScheduleRole)
    (n k : ℕ) (v : CopyScheduleVertex I n)
    (hv : CopyScheduleSurvives role n v) (hw : copyScheduleRole role n v = .pivot k) :
    n ≤ k ∧ ∃ i : I, role i = .pivot k ∧ v = copySchedulePositive n i := by
  induction n with
  | zero => exact ⟨Nat.zero_le _, v, hw, rfl⟩
  | succ n ih =>
    cases v with
    | inl q =>
      rcases q with ⟨b, v⟩
      change CopyScheduleSurvives role n v ∧ _ at hv
      change (copyScheduleRole role n v).afterCopy b = .pivot k at hw
      obtain ⟨rfl, hrole⟩ := (CopyScheduleRole.afterCopy_eq_pivot _ b k).mp hw
      have hnk : n < k := by
        have hc := hv.2
        rw [hrole] at hc
        simpa [CopyScheduleRole.copiedAt] using hc
      obtain ⟨_, i, hi, rfl⟩ := ih v hv.1 hrole
      exact ⟨by omega, i, hi, rfl⟩
    | inr v =>
      change CopyScheduleSurvives role n v ∧ _ ∧ _ at hv
      change copyScheduleRole role n v = .pivot k at hw
      obtain ⟨hnk, _⟩ := ih v hv.1 hw
      have hc := hv.2.1
      have he := hv.2.2
      rw [hw] at hc he
      have hnlt : ¬n < k := by simpa [CopyScheduleRole.copiedAt] using hc
      have hnne : n ≠ k := by simpa [CopyScheduleRole.erasedAt] using he
      omega

abbrev SurvivingPivotSlot {I : Type*} (role : I → CopyScheduleRole) (n k : ℕ) :=
  {v : CopyScheduleVertex I n // CopyScheduleSurvives role n v ∧ copyScheduleRole role n v = .pivot k}

noncomputable def survivingPivotEquiv {I : Type*} (role : I → CopyScheduleRole)
    (n k : ℕ) (hn : n ≤ k) :
    {i : I // role i = .pivot k} ≃ SurvivingPivotSlot role n k :=
  Equiv.ofBijective (fun i => ⟨copySchedulePositive n i.val,
    copyScheduleSurvives_positive role i.val k i.property n hn,
    copyScheduleRole_positive role i.val k i.property n⟩) (by
      constructor
      · intro i j h
        apply Subtype.ext
        exact copySchedulePositive_injective n (congrArg Subtype.val h)
      · intro v
        obtain ⟨_, i, hi, he⟩ := surviving_pivot_is_positive role n k v.val v.property.1 v.property.2
        exact ⟨⟨i, hi⟩, Subtype.ext he.symm⟩)

theorem surviving_pivot_card {I : Type*} [Fintype I] (role : I → CopyScheduleRole)
    (n k : ℕ) (hn : n ≤ k) :
    Nat.card (SurvivingPivotSlot role n k) = Nat.card {i : I // role i = .pivot k} := by
  classical
  exact (Nat.card_congr (survivingPivotEquiv role n k hn)).symm

/-- At its own step there is one active atom whenever the original group was
represented by one atom. Its internal prime constituents need no new copies. -/
theorem unique_active_pivot_atom {I : Type*} (role : I → CopyScheduleRole)
    (k : ℕ) (p : I) (hp : role p = .pivot k)
    (hunique : ∀ i, role i = .pivot k → i = p) :
    ∃! v : CopyScheduleVertex I k,
      CopyScheduleSurvives role k v ∧ copyScheduleRole role k v = .pivot k := by
  refine ⟨copySchedulePositive k p,
    ⟨copyScheduleSurvives_positive role p k hp k le_rfl,
      copyScheduleRole_positive role p k hp k⟩, ?_⟩
  intro v hv
  obtain ⟨_, i, hi, he⟩ := surviving_pivot_is_positive role k k v hv.1 hv.2
  simpa only [hunique i hi] using he

end Ostmann

end OAI
