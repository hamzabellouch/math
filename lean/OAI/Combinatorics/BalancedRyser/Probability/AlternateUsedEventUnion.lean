import OAI.Combinatorics.BalancedRyser.Local.LocalFourEventWitnesses
import OAI.Combinatorics.BalancedRyser.Local.LocalTwoReuseUsedEvents

namespace OAI

namespace Balanced.Local.AlternateUsedEventUnion

noncomputable section
open scoped Classical BigOperators
open UnusedOffsetProbability

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

abbrev UsedHitIndex (b κ : ℕ) := Fin (4 * b - κ) × (Fin b × Fin 4) × Bool
abbrev TripleIndex (b : ℕ) := (Fin b × Fin 4) × (Fin b × Fin 4) × (Fin b × Fin 4)

def UsedHit (P : EqualityPattern b κ) (a : DirectionAssignment F b κ)
    (bits : Bits b) (p : Point F) (z : UsedHitIndex b κ) (M : MergedPairs F) : Prop :=
  Admissible P a bits p M ∧ (∀ j, P.classOf z.2.1.1 j ≠ z.1) ∧
    OnLine (prescribedPoint P a bits M z.2.1) (constituent M (a.2 z.1) z.2.2)

def CollinearHit (P : EqualityPattern b κ) (a : DirectionAssignment F b κ)
    (bits : Bits b) (p : Point F) (z : TripleIndex b) (M : MergedPairs F) : Prop :=
  Admissible P a bits p M ∧
  z.1.1 ≠ z.2.1.1 ∧ z.1.1 ≠ z.2.2.1 ∧ z.2.1.1 ≠ z.2.2.1 ∧
  prescribedPoint P a bits M z.1 ≠ prescribedPoint P a bits M z.2.1 ∧
  prescribedPoint P a bits M z.1 ≠ prescribedPoint P a bits M z.2.2 ∧
  prescribedPoint P a bits M z.2.1 ≠ prescribedPoint P a bits M z.2.2 ∧
  OnLine (prescribedPoint P a bits M z.2.2)
    (joiningLine (prescribedPoint P a bits M z.1) (prescribedPoint P a bits M z.2.1)) ∧
  (∀ i, joiningLine (prescribedPoint P a bits M z.1)
    (prescribedPoint P a bits M z.2.1) ≠ lineThrough (a.1 i) p) ∧
  (∀ c s, joiningLine (prescribedPoint P a bits M z.1)
    (prescribedPoint P a bits M z.2.1) ≠ constituent M (a.2 c) s)

theorem admissible_usedPairExtra_iff (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (ha : Function.Injective a.2) (M : MergedPairs F) :
    (Admissible P a bits p M ∧ FourEvents.UsedPairExtra P a bits M) ↔
      ∃ z : UsedHitIndex b κ, UsedHit P a bits p z M := by
  rw [FourEvents.usedPairExtra_iff_indices P a bits M ha]
  constructor
  · rintro ⟨hadm,c,i,s,hnot,hhit⟩
    exact ⟨(c,i,s),hadm,hnot,hhit⟩
  · rintro ⟨⟨c,i,s⟩,hadm,hnot,hhit⟩
    exact ⟨hadm,c,i,s,hnot,hhit⟩

theorem admissible_forbiddenCollinearTriple_subset (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (M : MergedPairs F)
    (h : Admissible P a bits p M ∧ FourEvents.ForbiddenCollinearTriple P a bits p M) :
    ∃ z : TripleIndex b, CollinearHit P a bits p z M := by
  obtain ⟨i,j,k,hij,hik,hjk,hxy,hxz,hyz,hhit,htarget,hconst⟩ :=
    FourEvents.forbiddenCollinearTriple_joiningLine P a bits p M h.1.1 h.2
  exact ⟨(i,j,k),h.1,hij,hik,hjk,hxy,hxz,hyz,hhit,htarget,hconst⟩

theorem conditioned_exists_le_sum {I : Type*} [Fintype I]
    (A : MergedPairs F → Prop) (E : I → MergedPairs F → Prop) :
    conditionedOffsetProbability A (fun M => ∃ i, E i M) ≤
      ∑ i, conditionedOffsetProbability A (E i) := by
  unfold conditionedOffsetProbability
  rw [← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ (offsetProbability_nonneg A)
  have heq : (fun M => A M ∧ ∃ i, E i M) =
      (fun M => ∃ i, A M ∧ E i M) := by
    funext M
    apply propext
    constructor
    · rintro ⟨hA,i,hi⟩
      exact ⟨i,hA,hi⟩
    · rintro ⟨i,hA,hi⟩
      exact ⟨hA,i,hi⟩
  rw [heq]
  exact offsetProbability_exists_le_sum _

theorem usedPair_probability_le_sum (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (ha : Function.Injective a.2) :
    conditionedOffsetProbability (Aligned P a bits p)
      (fun M => Admissible P a bits p M ∧ FourEvents.UsedPairExtra P a bits M) ≤
      ∑ z : UsedHitIndex b κ,
        conditionedOffsetProbability (Aligned P a bits p) (UsedHit P a bits p z) := by
  have heq : (fun M => Admissible P a bits p M ∧ FourEvents.UsedPairExtra P a bits M) =
      (fun M => ∃ z : UsedHitIndex b κ, UsedHit P a bits p z M) := by
    funext M
    exact propext (admissible_usedPairExtra_iff P a bits p ha M)
  rw [heq]
  exact conditioned_exists_le_sum _ _

theorem collinear_probability_le_sum (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F) :
    conditionedOffsetProbability (Aligned P a bits p)
      (fun M => Admissible P a bits p M ∧ FourEvents.ForbiddenCollinearTriple P a bits p M) ≤
      ∑ z : TripleIndex b,
        conditionedOffsetProbability (Aligned P a bits p) (CollinearHit P a bits p z) := by
  exact (conditionedOffsetProbability_mono (Aligned P a bits p)
    (admissible_forbiddenCollinearTriple_subset P a bits p)).trans
      (conditioned_exists_le_sum _ _)

def injectionMean (P : EqualityPattern b κ) (bits : Bits b) (p : Point F)
    (E : DirectionAssignment F b κ → MergedPairs F → Prop) : ℝ :=
  (∑ e : DirectionToken b κ ↪ Direction F,
    conditionedOffsetProbability (Aligned P (tokenInjectionEquiv F b κ e).1 bits p)
      (E (tokenInjectionEquiv F b κ e).1)) /
        Fintype.card (DirectionToken b κ ↪ Direction F)

theorem injectionMean_le_sum {I : Type*} [Fintype I]
    (P : EqualityPattern b κ) (bits : Bits b) (p : Point F)
    (E : DirectionAssignment F b κ → MergedPairs F → Prop)
    (G : I → DirectionAssignment F b κ → MergedPairs F → Prop)
    (h : ∀ a, AllTokensDistinct a →
      conditionedOffsetProbability (Aligned P a bits p) (E a) ≤
        ∑ i, conditionedOffsetProbability (Aligned P a bits p) (G i a)) :
    injectionMean P bits p E ≤ ∑ i, injectionMean P bits p (G i) := by
  unfold injectionMean
  rw [← Finset.sum_div, Finset.sum_comm]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact Finset.sum_le_sum (fun e _ => h _ (tokenInjectionEquiv F b κ e).2)

theorem card_usedHitIndex_le (b κ : ℕ) : Fintype.card (UsedHitIndex b κ) ≤ 32 * b ^ 2 := by
  simp only [UsedHitIndex, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  calc
    _ ≤ (4*b) * (b*4) * 2 := by
      simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right (b*4*2) (Nat.sub_le (4*b) κ)
    _ = _ := by ring

theorem card_tripleIndex (b : ℕ) : Fintype.card (TripleIndex b) = 64 * b ^ 3 := by
  simp only [TripleIndex, Fintype.card_prod, Fintype.card_fin]
  ring

theorem usedPair_mean_le (P : EqualityPattern b κ) (bits : Bits b) (p : Point F)
    (ε : ℝ) (hε : 0 ≤ ε)
    (h : ∀ z : UsedHitIndex b κ,
      injectionMean P bits p (fun a => UsedHit P a bits p z) ≤ ε) :
    injectionMean P bits p (fun a M =>
      Admissible P a bits p M ∧ FourEvents.UsedPairExtra P a bits M) ≤
        32 * (b : ℝ)^2 * ε := by
  apply (injectionMean_le_sum P bits p _ (fun z a => UsedHit P a bits p z)
    (fun a ha => usedPair_probability_le_sum P a bits p
      (allTokensDistinct_eligible P a ha).2.1)).trans
  calc
    _ ≤ ∑ _z : UsedHitIndex b κ, ε := Finset.sum_le_sum (fun z _ => h z)
    _ = (Fintype.card (UsedHitIndex b κ) : ℝ) * ε := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast card_usedHitIndex_le b κ) hε

theorem collinear_mean_le (P : EqualityPattern b κ) (bits : Bits b) (p : Point F)
    (ε : ℝ)
    (h : ∀ z : TripleIndex b,
      injectionMean P bits p (fun a => CollinearHit P a bits p z) ≤ ε) :
    injectionMean P bits p (fun a M =>
      Admissible P a bits p M ∧ FourEvents.ForbiddenCollinearTriple P a bits p M) ≤
        64 * (b : ℝ)^3 * ε := by
  apply (injectionMean_le_sum P bits p _ (fun z a => CollinearHit P a bits p z)
    (fun a _ => collinear_probability_le_sum P a bits p)).trans
  calc
    _ ≤ ∑ _z : TripleIndex b, ε := Finset.sum_le_sum (fun z _ => h z)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        card_tripleIndex, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]

end
end Balanced.Local.AlternateUsedEventUnion

end OAI
