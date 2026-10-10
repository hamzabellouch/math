import OAI.Combinatorics.BalancedRyser.Local.Local
import OAI.Combinatorics.BalancedRyser.Local.LocalPatternCodes
import OAI.Combinatorics.BalancedRyser.Probability.SparsePatterns

namespace OAI

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Balanced.Local

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ} {P Q : EqualityPattern b κ}

theorem exists_classRelabeling
    (h : ∀ i j : Fin b × Fin 4,
      (P.classOf i.1 i.2 = P.classOf j.1 j.2 ↔
        Q.classOf i.1 i.2 = Q.classOf j.1 j.2)) :
    ∃ e : Fin (4 * b - κ) ≃ Fin (4 * b - κ),
      ∀ i j, e (P.classOf i j) = Q.classOf i j := by
  obtain ⟨e, he⟩ := SparsePatterns.exists_relabeling_of_same_pattern
    (fun i : Fin b × Fin 4 => P.classOf i.1 i.2)
    (fun i : Fin b × Fin 4 => Q.classOf i.1 i.2)
    P.everyClass Q.everyClass h
  exact ⟨e, fun i j => he (i, j)⟩

def relabelAssignment (e : Fin (4 * b - κ) ≃ Fin (4 * b - κ)) :
    DirectionAssignment F b κ ≃ DirectionAssignment F b κ :=
  Equiv.prodCongr (Equiv.refl _) (Equiv.arrowCongr e (Equiv.refl _))

variable (e : Fin (4 * b - κ) ≃ Fin (4 * b - κ))
variable (he : ∀ i j, e (P.classOf i j) = Q.classOf i j)

omit [Field F] [Fintype F] [DecidableEq F] in
@[simp] theorem relabelAssignment_target (a : DirectionAssignment F b κ) :
    (relabelAssignment e a).1 = a.1 := rfl

include he

omit [Field F] [Fintype F] [DecidableEq F] in
theorem relabelAssignment_generator (a : DirectionAssignment F b κ)
    (i : Fin b) (j : Fin 4) :
    (relabelAssignment e a).2 (Q.classOf i j) = a.2 (P.classOf i j) := by
  change a.2 (e.symm (Q.classOf i j)) = a.2 (P.classOf i j)
  rw [← he i j, e.symm_apply_apply]

omit [Field F] [Fintype F] [DecidableEq F] in
theorem eligible_relabelAssignment (a : DirectionAssignment F b κ) :
    Eligible Q (relabelAssignment e a) ↔ Eligible P a := by
  have hinj : Function.Injective (relabelAssignment e a).2 ↔
      Function.Injective a.2 := by
    change Function.Injective (a.2 ∘ e.symm) ↔ Function.Injective a.2
    constructor
    · intro h x y hxy
      have hh : e x = e y := h (by simpa using hxy)
      exact e.injective hh
    · intro h
      exact h.comp e.symm.injective
  simp only [Eligible, relabelAssignment_target, hinj,
    relabelAssignment_generator e he]

omit [Field F] [Fintype F] [DecidableEq F] in
theorem prescribedTuple_relabelAssignment (a : DirectionAssignment F b κ)
    (bits : Bits b) (i : Fin b) :
    prescribedTuple Q (relabelAssignment e a) bits i =
      prescribedTuple P a bits i := by
  unfold prescribedTuple
  congr 1
  funext j
  exact relabelAssignment_generator e he a i j

omit [Fintype F] [DecidableEq F] in
theorem prescribedPoint_relabelAssignment (a : DirectionAssignment F b κ)
    (bits : Bits b) (M : MergedPairs F) :
    prescribedPoint Q (relabelAssignment e a) bits M =
      prescribedPoint P a bits M := by
  funext ij
  simp only [prescribedPoint, prescribedTuple_relabelAssignment e he]

omit [Fintype F] [DecidableEq F] in
theorem aligned_relabelAssignment (a : DirectionAssignment F b κ)
    (bits : Bits b) (p : Point F) (M : MergedPairs F) :
    Aligned Q (relabelAssignment e a) bits p M ↔ Aligned P a bits p M := by
  simp only [Aligned, prescribedPoint_relabelAssignment e he,
    relabelAssignment_target]

theorem admissible_relabelAssignment (a : DirectionAssignment F b κ)
    (bits : Bits b) (p : Point F) (M : MergedPairs F) :
    Admissible Q (relabelAssignment e a) bits p M ↔ Admissible P a bits p M := by
  simp only [Admissible, aligned_relabelAssignment e he,
    prescribedPoint_relabelAssignment e he, relabelAssignment_target]

omit [Fintype F] in
theorem prescribedDesignated_relabelAssignment (a : DirectionAssignment F b κ)
    (bits : Bits b) (M : MergedPairs F) :
    prescribedDesignated Q (relabelAssignment e a) bits M =
      prescribedDesignated P a bits M := by
  simp only [prescribedDesignated, prescribedPoint_relabelAssignment e he]

theorem prescribedPartners_relabelAssignment (a : DirectionAssignment F b κ)
    (bits : Bits b) (p : Point F) (M : MergedPairs F) :
    prescribedPartners Q (relabelAssignment e a) bits p M =
      prescribedPartners P a bits p M := by
  simp only [prescribedPartners, prescribedDesignated_relabelAssignment e he]

omit he in
theorem allowedPiece_relabelAssignment (a : DirectionAssignment F b κ)
    (p : Point F) (M : MergedPairs F) (x : LocalPiece F) :
    AllowedPiece (relabelAssignment e a) p M x ↔ AllowedPiece a p M x := by
  cases x with
  | inl U => rfl
  | inr x =>
      cases x <;> rfl

theorem badCover_relabelAssignment (a : DirectionAssignment F b κ)
    (bits : Bits b) (p : Point F) (M : MergedPairs F) :
    BadCover Q (relabelAssignment e a) bits p M ↔ BadCover P a bits p M := by
  simp only [BadCover, prescribedDesignated_relabelAssignment e he,
    prescribedPartners_relabelAssignment e he, allowedPiece_relabelAssignment]

theorem admissibleBadCover_relabelAssignment (a : DirectionAssignment F b κ)
    (bits : Bits b) (p : Point F) (M : MergedPairs F) :
    AdmissibleBadCover Q (relabelAssignment e a) bits p M ↔
      AdmissibleBadCover P a bits p M := by
  simp only [AdmissibleBadCover, admissible_relabelAssignment e he,
    badCover_relabelAssignment e he]

theorem direction_sum_eq_of_relabeling (bits : Bits b) (p : Point F) :
    (∑ a : DirectionAssignment F b κ,
      if Eligible P a then offsetProbability (fun M =>
        Aligned P a bits p M ∧ AdmissibleBadCover P a bits p M) else 0) =
    ∑ a : DirectionAssignment F b κ,
      if Eligible Q a then offsetProbability (fun M =>
        Aligned Q a bits p M ∧ AdmissibleBadCover Q a bits p M) else 0 := by
  classical
  apply Fintype.sum_equiv (relabelAssignment e)
  intro a
  simp only [eligible_relabelAssignment e he, aligned_relabelAssignment e he,
    admissibleBadCover_relabelAssignment e he]

theorem conditioned_badCover_eq_of_relabeling (a : DirectionAssignment F b κ)
    (bits : Bits b) (p : Point F) :
    conditionedOffsetProbability (Aligned Q (relabelAssignment e a) bits p)
      (AdmissibleBadCover Q (relabelAssignment e a) bits p) =
    conditionedOffsetProbability (Aligned P a bits p)
      (AdmissibleBadCover P a bits p) := by
  have hA : Aligned Q (relabelAssignment e a) bits p = Aligned P a bits p :=
    funext fun M => propext (aligned_relabelAssignment e he a bits p M)
  have hB : AdmissibleBadCover Q (relabelAssignment e a) bits p =
      AdmissibleBadCover P a bits p :=
    funext fun M => propext (admissibleBadCover_relabelAssignment e he a bits p M)
  rw [hA, hB]

omit he in

theorem direction_sum_eq_of_same_pattern
    (h : ∀ i j : Fin b × Fin 4,
      (P.classOf i.1 i.2 = P.classOf j.1 j.2 ↔
        Q.classOf i.1 i.2 = Q.classOf j.1 j.2))
    (bits : Bits b) (p : Point F) :
    (∑ a : DirectionAssignment F b κ,
      if Eligible P a then offsetProbability (fun M =>
        Aligned P a bits p M ∧ AdmissibleBadCover P a bits p M) else 0) =
    ∑ a : DirectionAssignment F b κ,
      if Eligible Q a then offsetProbability (fun M =>
        Aligned Q a bits p M ∧ AdmissibleBadCover Q a bits p M) else 0 := by
  obtain ⟨e, he⟩ := exists_classRelabeling h
  exact direction_sum_eq_of_relabeling e he bits p

omit he in

def directionBadCoverMass (P : EqualityPattern b κ) (bits : Bits b) (p : Point F) : ℝ :=
  ∑ a : DirectionAssignment F b κ,
    if Eligible P a then offsetProbability (fun M =>
      Aligned P a bits p M ∧ AdmissibleBadCover P a bits p M) else 0

omit he in

theorem exists_directionSum_representatives (hb : 1 ≤ b) (hκ : κ ≤ 2) :
    ∃ R : Finset (EqualityPattern b κ), R.card ≤ (4 * b) ^ 4 ∧
      ∀ P : EqualityPattern b κ, ∃ Q ∈ R, ∀ (bits : Bits b) (p : Point F),
        directionBadCoverMass P bits p = directionBadCoverMass Q bits p := by
  obtain ⟨R, hR, hrep⟩ := PatternCodes.exists_pattern_representatives hb hκ
  refine ⟨R, hR, ?_⟩
  intro P
  obtain ⟨Q, hQ, hPQ⟩ := hrep P
  exact ⟨Q, hQ, fun bits p => direction_sum_eq_of_same_pattern hPQ bits p⟩

omit he in

theorem exists_representative_test_family (hb : 1 ≤ b) (hκ : κ ≤ 2) :
    ∃ R : Finset (EqualityPattern b κ), R.card ≤ (4 * b) ^ 4 ∧
      ∀ bound : Bits b → Point F → ℝ,
        (∀ P : EqualityPattern b κ, ∀ bits p,
          directionBadCoverMass P bits p ≤ bound bits p) ↔
        (∀ Q ∈ R, ∀ bits p, directionBadCoverMass Q bits p ≤ bound bits p) := by
  obtain ⟨R, hR, hrep⟩ := exists_directionSum_representatives (F := F) hb hκ
  refine ⟨R, hR, fun bound => ⟨fun h Q _ => h Q, ?_⟩⟩
  intro h P bits p
  obtain ⟨Q, hQ, heq⟩ := hrep P
  rw [heq bits p]
  exact h Q hQ bits p

end Balanced.Local

end

end OAI
