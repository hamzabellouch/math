import OAI.Combinatorics.BalancedRyser.Local.LocalFourEventProbability
import OAI.Combinatorics.BalancedRyser.Local.LocalFourEventWitnesses

namespace OAI

namespace Balanced.Local.UsedEventUnion

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

open UnusedOffsetProbability

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

abbrev UsedWitness (b κ : ℕ) :=
  Fin (4 * b - κ) × (Fin b × Fin 4) × Bool

abbrev TripleWitness (b : ℕ) :=
  (Fin b × Fin 4) × (Fin b × Fin 4) × (Fin b × Fin 4)

def usedConstituentTest (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (c : Fin (4 * b - κ)) (ij : Fin b × Fin 4) (s : Bool)
    (M : MergedPairs F) : Prop :=
  Admissible P a bits p M ∧ (∀ j, P.classOf ij.1 j ≠ c) ∧
    OnLine (prescribedPoint P a bits M ij) (constituent M (a.2 c) s)

def collinearTest (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (i j k : Fin b × Fin 4) (M : MergedPairs F) : Prop :=
  Admissible P a bits p M ∧
    i.1 ≠ j.1 ∧ i.1 ≠ k.1 ∧ j.1 ≠ k.1 ∧
    prescribedPoint P a bits M i ≠ prescribedPoint P a bits M j ∧
    prescribedPoint P a bits M i ≠ prescribedPoint P a bits M k ∧
    prescribedPoint P a bits M j ≠ prescribedPoint P a bits M k ∧
    OnLine (prescribedPoint P a bits M k)
      (joiningLine (prescribedPoint P a bits M i) (prescribedPoint P a bits M j)) ∧
    (∀ t, joiningLine (prescribedPoint P a bits M i) (prescribedPoint P a bits M j) ≠
      lineThrough (a.1 t) p) ∧
    (∀ c s, joiningLine (prescribedPoint P a bits M i) (prescribedPoint P a bits M j) ≠
      constituent M (a.2 c) s)

theorem admissible_usedPairExtra_iff_exists
    (P : EqualityPattern b κ) (a : DirectionAssignment F b κ)
    (bits : Bits b) (p : Point F) (M : MergedPairs F)
    (ha : Function.Injective a.2) :
    (Admissible P a bits p M ∧ FourEvents.UsedPairExtra P a bits M) ↔
      ∃ z : UsedWitness b κ,
        usedConstituentTest P a bits p z.1 z.2.1 z.2.2 M := by
  constructor
  · rintro ⟨hA, hE⟩
    obtain ⟨c, ij, s, hn, hi⟩ :=
      (FourEvents.usedPairExtra_iff_indices P a bits M ha).mp hE
    exact ⟨(c, ij, s), hA, hn, hi⟩
  · rintro ⟨⟨c, ij, s⟩, hA, hn, hi⟩
    exact ⟨hA, (FourEvents.usedPairExtra_iff_indices P a bits M ha).mpr
      ⟨c, ij, s, hn, hi⟩⟩

theorem admissible_forbiddenTriple_imp_exists
    (P : EqualityPattern b κ) (a : DirectionAssignment F b κ)
    (bits : Bits b) (p : Point F) (M : MergedPairs F)
    (h : Admissible P a bits p M ∧
      FourEvents.ForbiddenCollinearTriple P a bits p M) :
    ∃ z : TripleWitness b, collinearTest P a bits p z.1 z.2.1 z.2.2 M := by
  obtain ⟨i, j, k, htest⟩ :=
    FourEvents.forbiddenCollinearTriple_joiningLine P a bits p M h.1.1 h.2
  exact ⟨(i, j, k), h.1, htest⟩

theorem conditionedOffsetProbability_exists_le_sum {ι : Type*} [Fintype ι]
    (A : MergedPairs F → Prop) (E : ι → MergedPairs F → Prop) :
    conditionedOffsetProbability A (fun M => ∃ i, E i M) ≤
      ∑ i, conditionedOffsetProbability A (E i) := by
  simp_rw [conditionedOffsetProbability, ← exists_and_left]
  rw [← Finset.sum_div]
  exact div_le_div_of_nonneg_right
    (offsetProbability_exists_le_sum (fun i M => A M ∧ E i M))
    (offsetProbability_nonneg A)

theorem conditioned_usedPairExtra_le_sum
    (P : EqualityPattern b κ) (a : DirectionAssignment F b κ)
    (bits : Bits b) (p : Point F) (ha : Function.Injective a.2) :
    conditionedOffsetProbability (Aligned P a bits p)
      (fun M => Admissible P a bits p M ∧ FourEvents.UsedPairExtra P a bits M) ≤
      ∑ z : UsedWitness b κ, conditionedOffsetProbability (Aligned P a bits p)
        (usedConstituentTest P a bits p z.1 z.2.1 z.2.2) := by
  apply (conditionedOffsetProbability_mono (Aligned P a bits p)
    (fun M h => (admissible_usedPairExtra_iff_exists P a bits p M ha).mp h)).trans
  exact conditionedOffsetProbability_exists_le_sum _ _

theorem conditioned_forbiddenTriple_le_sum
    (P : EqualityPattern b κ) (a : DirectionAssignment F b κ)
    (bits : Bits b) (p : Point F) :
    conditionedOffsetProbability (Aligned P a bits p)
      (fun M => Admissible P a bits p M ∧
        FourEvents.ForbiddenCollinearTriple P a bits p M) ≤
      ∑ z : TripleWitness b, conditionedOffsetProbability (Aligned P a bits p)
        (collinearTest P a bits p z.1 z.2.1 z.2.2) := by
  apply (conditionedOffsetProbability_mono (Aligned P a bits p)
    (fun M h => admissible_forbiddenTriple_imp_exists P a bits p M h)).trans
  exact conditionedOffsetProbability_exists_le_sum _ _

def alignedAverage (P : EqualityPattern b κ) (bits : Bits b) (p : Point F)
    (w : DirectionAssignment F b κ → ℝ)
    (E : DirectionAssignment F b κ → MergedPairs F → Prop) : ℝ :=
  ∑ a, w a * conditionedOffsetProbability (Aligned P a bits p) (E a)

theorem alignedAverage_mono (P : EqualityPattern b κ) (bits : Bits b)
    (p : Point F) (w : DirectionAssignment F b κ → ℝ) (hw : ∀ a, 0 ≤ w a)
    {E G : DirectionAssignment F b κ → MergedPairs F → Prop}
    (h : ∀ a, w a ≠ 0 → ∀ M, E a M → G a M) :
    alignedAverage P bits p w E ≤ alignedAverage P bits p w G := by
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : w a = 0
  · simp only [ha, zero_mul, le_refl]
  · exact mul_le_mul_of_nonneg_left
      (conditionedOffsetProbability_mono _ (h a ha)) (hw a)

theorem alignedAverage_exists_le_sum {ι : Type*} [Fintype ι]
    (P : EqualityPattern b κ) (bits : Bits b) (p : Point F)
    (w : DirectionAssignment F b κ → ℝ) (hw : ∀ a, 0 ≤ w a)
    (E : ι → DirectionAssignment F b κ → MergedPairs F → Prop) :
    alignedAverage P bits p w (fun a M => ∃ i, E i a M) ≤
      ∑ i, alignedAverage P bits p w (E i) := by
  unfold alignedAverage
  calc
    (∑ a, w a * conditionedOffsetProbability (Aligned P a bits p)
        (fun M => ∃ i, E i a M)) ≤
        ∑ a, w a * ∑ i, conditionedOffsetProbability (Aligned P a bits p) (E i a) := by
      apply Finset.sum_le_sum
      intro a _
      exact mul_le_mul_of_nonneg_left
        (conditionedOffsetProbability_exists_le_sum _ _) (hw a)
    _ = _ := by
      simp_rw [Finset.mul_sum]
      exact Finset.sum_comm

theorem card_usedWitness_le (b κ : ℕ) :
    Fintype.card (UsedWitness b κ) ≤ 32 * b ^ 2 := by
  simp only [UsedWitness, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  calc
    (4 * b - κ) * (b * 4 * 2) ≤ (4 * b) * (b * 4 * 2) :=
      Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    _ = _ := by ring

theorem card_tripleWitness (b : ℕ) :
    Fintype.card (TripleWitness b) = 64 * b ^ 3 := by
  simp only [TripleWitness, Fintype.card_prod, Fintype.card_fin]
  ring

theorem alignedAverage_usedPairExtra_le
    (P : EqualityPattern b κ) (bits : Bits b) (p : Point F)
    (w : DirectionAssignment F b κ → ℝ) (hw : ∀ a, 0 ≤ w a)
    (ha : ∀ a, w a ≠ 0 → Function.Injective a.2)
    {t : ℝ} (ht : 0 ≤ t)
    (htest : ∀ c ij s, alignedAverage P bits p w
      (fun a => usedConstituentTest P a bits p c ij s) ≤ t) :
    alignedAverage P bits p w
      (fun a M => Admissible P a bits p M ∧ FourEvents.UsedPairExtra P a bits M) ≤
        32 * (b : ℝ) ^ 2 * t := by
  have hmono := alignedAverage_mono P bits p w hw
    (fun a hwa M h => (admissible_usedPairExtra_iff_exists P a bits p M (ha a hwa)).mp h)
  apply hmono.trans
  apply (alignedAverage_exists_le_sum P bits p w hw
    (fun z : UsedWitness b κ => fun a =>
      usedConstituentTest P a bits p z.1 z.2.1 z.2.2)).trans
  calc
    (∑ z : UsedWitness b κ, alignedAverage P bits p w
        (fun a => usedConstituentTest P a bits p z.1 z.2.1 z.2.2)) ≤
        ∑ _z : UsedWitness b κ, t := Finset.sum_le_sum (fun z _ => htest z.1 z.2.1 z.2.2)
    _ = (Fintype.card (UsedWitness b κ) : ℝ) * t := by simp
    _ ≤ 32 * (b : ℝ) ^ 2 * t := by
      apply mul_le_mul_of_nonneg_right _ ht
      exact_mod_cast card_usedWitness_le b κ

theorem alignedAverage_forbiddenTriple_le
    (P : EqualityPattern b κ) (bits : Bits b) (p : Point F)
    (w : DirectionAssignment F b κ → ℝ) (hw : ∀ a, 0 ≤ w a)
    {t : ℝ}
    (htest : ∀ i j k, alignedAverage P bits p w
      (fun a => collinearTest P a bits p i j k) ≤ t) :
    alignedAverage P bits p w
      (fun a M => Admissible P a bits p M ∧
        FourEvents.ForbiddenCollinearTriple P a bits p M) ≤
        64 * (b : ℝ) ^ 3 * t := by
  have hmono := alignedAverage_mono P bits p w hw
    (fun a _ M h => admissible_forbiddenTriple_imp_exists P a bits p M h)
  apply hmono.trans
  apply (alignedAverage_exists_le_sum P bits p w hw
    (fun z : TripleWitness b => fun a => collinearTest P a bits p z.1 z.2.1 z.2.2)).trans
  calc
    (∑ z : TripleWitness b, alignedAverage P bits p w
        (fun a => collinearTest P a bits p z.1 z.2.1 z.2.2)) ≤
        ∑ _z : TripleWitness b, t := Finset.sum_le_sum (fun z _ => htest z.1 z.2.1 z.2.2)
    _ = (Fintype.card (TripleWitness b) : ℝ) * t := by simp
    _ = 64 * (b : ℝ) ^ 3 * t := by rw [card_tripleWitness]; push_cast; rfl

end
end Balanced.Local.UsedEventUnion

end OAI
