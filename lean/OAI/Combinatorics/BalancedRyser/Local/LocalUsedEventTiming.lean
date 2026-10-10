import OAI.Combinatorics.BalancedRyser.Local.AlignedUsedTestTransport
import OAI.Combinatorics.BalancedRyser.Local.LocalUsedEventMean

namespace OAI

namespace Balanced.Local.UsedEventUnion

noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

omit [Fintype F] in
theorem geometricCollinearTest_rotate
    (P : EqualityPattern b κ) (a : DirectionAssignment F b κ)
    (bits : Bits b) (p : Point F) (M : MergedPairs F)
    (i j k : Fin b × Fin 4)
    (h : geometricCollinearTest P a bits p i j k M) :
    geometricCollinearTest P a bits p j k i M := by
  rcases h with ⟨hg, hij, hik, hjk, hxy, hxz, hyz, hline, ht, hu⟩
  have heq : joiningLine (prescribedPoint P a bits M j) (prescribedPoint P a bits M k) =
      joiningLine (prescribedPoint P a bits M i) (prescribedPoint P a bits M j) :=
    eq_of_two_common_points _ _ hyz _ _ (onLine_joiningLine_left _ _)
      (onLine_joiningLine_right _ _) (onLine_joiningLine_right _ _) hline
  refine ⟨hg, hjk, hij.symm, hik.symm, hyz, hxy.symm, hxz.symm, ?_, ?_, ?_⟩
  · rw [heq]
    exact onLine_joiningLine_left _ _
  · simpa only [heq] using ht
  · simpa only [heq] using hu

omit [Fintype F] in
theorem geometricCollinearTest_rotate_twice
    (P : EqualityPattern b κ) (a : DirectionAssignment F b κ)
    (bits : Bits b) (p : Point F) (M : MergedPairs F)
    (i j k : Fin b × Fin 4)
    (h : geometricCollinearTest P a bits p i j k M) :
    geometricCollinearTest P a bits p k i j M :=
  geometricCollinearTest_rotate P a bits p M j k i
    (geometricCollinearTest_rotate P a bits p M i j k h)

omit [Fintype F] in
theorem geometricCollinearTest_latest
    (P : EqualityPattern b κ) (a : DirectionAssignment F b κ)
    (bits : Bits b) (p : Point F) (M : MergedPairs F)
    (rank : Fin b → ℕ) (hrank : Function.Injective rank)
    (i j k : Fin b × Fin 4)
    (h : geometricCollinearTest P a bits p i j k M) :
    (rank i.1 < rank k.1 ∧ rank j.1 < rank k.1 ∧
      geometricCollinearTest P a bits p i j k M) ∨
    (rank j.1 < rank i.1 ∧ rank k.1 < rank i.1 ∧
      geometricCollinearTest P a bits p j k i M) ∨
    (rank k.1 < rank j.1 ∧ rank i.1 < rank j.1 ∧
      geometricCollinearTest P a bits p k i j M) := by
  have hij : rank i.1 ≠ rank j.1 := fun he => h.2.1 (hrank he)
  have hik : rank i.1 ≠ rank k.1 := fun he => h.2.2.1 (hrank he)
  have hjk : rank j.1 ≠ rank k.1 := fun he => h.2.2.2.1 (hrank he)
  by_cases hik' : rank i.1 < rank k.1
  · by_cases hjk' : rank j.1 < rank k.1
    · exact Or.inl ⟨hik', hjk', h⟩
    · exact Or.inr (Or.inr ⟨by omega, by omega,
        geometricCollinearTest_rotate_twice P a bits p M i j k h⟩)
  · by_cases hji : rank j.1 < rank i.1
    · exact Or.inr (Or.inl ⟨hji, by omega,
        geometricCollinearTest_rotate P a bits p M i j k h⟩)
    · exact Or.inr (Or.inr ⟨by omega, by omega,
        geometricCollinearTest_rotate_twice P a bits p M i j k h⟩)

theorem collinearTest_rotate
    (P : EqualityPattern b κ) (a : DirectionAssignment F b κ)
    (bits : Bits b) (p : Point F) (M : MergedPairs F)
    (i j k : Fin b × Fin 4) (h : collinearTest P a bits p i j k M) :
    collinearTest P a bits p j k i M :=
  ⟨h.1, (geometricCollinearTest_rotate P a bits p M i j k
    (collinearTest_implies_geometric P a bits p i j k M h)).2⟩

theorem injectionAverage_mono
    (P : EqualityPattern b κ) (bits : Bits b) (p : Point F)
    (E G : DirectionAssignment F b κ → MergedPairs F → Prop)
    (h : ∀ a M, E a M → G a M) :
    injectionAverage P bits p E ≤ injectionAverage P bits p G := by
  unfold injectionAverage
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro e _
  exact UnusedOffsetProbability.conditionedOffsetProbability_mono _
    (h (tokenInjectionEquiv F b κ e).1)

theorem collinear_injectionAverage_le_of_latest
    (P : EqualityPattern b κ) (bits : Bits b) (p : Point F)
    (rank : Fin b → ℕ) (hrank : Function.Injective rank)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ i j k : Fin b × Fin 4,
      rank i.1 < rank k.1 → rank j.1 < rank k.1 →
      injectionAverage P bits p (fun a => collinearTest P a bits p i j k) ≤ C)
    (i j k : Fin b × Fin 4) :
    injectionAverage P bits p (fun a => collinearTest P a bits p i j k) ≤ C := by
  classical
  by_cases hij : i.1 = j.1
  · simpa [injectionAverage, conditionedOffsetProbability, offsetProbability,
      collinearTest, hij] using hC
  by_cases hik : i.1 = k.1
  · simpa [injectionAverage, conditionedOffsetProbability, offsetProbability,
      collinearTest, hik] using hC
  by_cases hjk : j.1 = k.1
  · simpa [injectionAverage, conditionedOffsetProbability, offsetProbability,
      collinearTest, hjk] using hC
  have hijr : rank i.1 ≠ rank j.1 := fun he => hij (hrank he)
  have hikr : rank i.1 ≠ rank k.1 := fun he => hik (hrank he)
  have hjkr : rank j.1 ≠ rank k.1 := fun he => hjk (hrank he)
  have hrot : injectionAverage P bits p (fun a => collinearTest P a bits p i j k) ≤
      injectionAverage P bits p (fun a => collinearTest P a bits p j k i) :=
    injectionAverage_mono P bits p _ _ (fun a M h => collinearTest_rotate P a bits p M i j k h)
  have hrot2 : injectionAverage P bits p (fun a => collinearTest P a bits p j k i) ≤
      injectionAverage P bits p (fun a => collinearTest P a bits p k i j) :=
    injectionAverage_mono P bits p _ _ (fun a M h => collinearTest_rotate P a bits p M j k i h)
  by_cases hik' : rank i.1 < rank k.1
  · by_cases hjk' : rank j.1 < rank k.1
    · exact hbound i j k hik' hjk'
    · exact (hrot.trans hrot2).trans (hbound k i j (by omega) (by omega))
  · by_cases hji : rank j.1 < rank i.1
    · exact hrot.trans (hbound j k i hji (by omega))
    · exact (hrot.trans hrot2).trans (hbound k i j (by omega) (by omega))

end
end Balanced.Local.UsedEventUnion

end OAI
