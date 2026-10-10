import Mathlib.Tactic
import OAI.Combinatorics.BalancedRyser.Local.Local
import OAI.Combinatorics.BalancedRyser.Local.LocalPrescribedGeometry

namespace OAI

namespace Balanced.Local.FourEvents

noncomputable section
open scoped Classical BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

def tuplePoints (P : EqualityPattern b κ) (a : DirectionAssignment F b κ)
    (bits : Bits b) (M : MergedPairs F) (i : Fin b) : Finset (Point F) :=
  Finset.univ.image (fun j => prescribedPoint P a bits M (i, j))

def usedDirections (a : DirectionAssignment F b κ) : Finset (Direction F) :=
  Finset.univ.image a.2

def usingTuples (P : EqualityPattern b κ) (a : DirectionAssignment F b κ)
    (d : Direction F) : Finset (Fin b) :=
  Finset.univ.filter (fun i => ∃ j, a.2 (P.classOf i j) = d)

def classUseCount (P : EqualityPattern b κ) (c : Fin (4 * b - κ)) : ℕ :=
  (Finset.univ.filter (fun i => ∃ j, P.classOf i j = c)).card

omit [Field F] [Fintype F] in
@[simp] theorem usingTuples_class_card (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (ha : Function.Injective a.2)
    (c : Fin (4 * b - κ)) :
    (usingTuples P a (a.2 c)).card = classUseCount P c := by
  simp only [usingTuples, classUseCount, ha.eq_iff]

theorem classUseCount_pos (P : EqualityPattern b κ) (c : Fin (4 * b - κ)) :
    0 < classUseCount P c := by
  obtain ⟨⟨i, j⟩, hij⟩ := P.everyClass c
  apply Finset.card_pos.mpr
  exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨j, hij⟩⟩⟩

theorem sum_classUseCount (P : EqualityPattern b κ) :
    ∑ c, classUseCount P c = 4 * b := by
  simp only [classUseCount, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  have hi (i : Fin b) :
      (∑ c : Fin (4 * b - κ), if ∃ j, P.classOf i j = c then 1 else 0) = 4 := by
    have hs : (Finset.univ.filter (fun c => ∃ j, P.classOf i j = c)) =
        Finset.univ.image (P.classOf i) := by
      ext c
      simp
    have hc := Finset.card_image_of_injective (Finset.univ : Finset (Fin 4))
      (P.withinTuple i)
    rw [← hs] at hc
    rw [Finset.card_eq_sum_ones, Finset.sum_filter] at hc
    simpa only [Finset.card_univ, Fintype.card_fin] using hc
  simp_rw [hi]
  simp [Nat.mul_comm]

theorem sum_class_excess (P : EqualityPattern b κ) (hκ : κ ≤ 4 * b) :
    ∑ c, (classUseCount P c - 1) = κ := by
  rw [Finset.sum_tsub_distrib]
  · rw [sum_classUseCount]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      mul_one]
    omega
  · intro c _
    exact classUseCount_pos P c

omit [Field F] [Fintype F] in
theorem usingTuples_eq_empty_of_not_used (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (d : Direction F)
    (hd : d ∉ usedDirections a) : usingTuples P a d = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  obtain ⟨j, hj⟩ := (Finset.mem_filter.mp hi).2
  exact hd (Finset.mem_image.mpr ⟨P.classOf i j, Finset.mem_univ _, hj⟩)

omit [Field F] in

theorem sum_direction_excess (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (ha : Function.Injective a.2)
    (hκ : κ ≤ 4 * b) :
    ∑ d : Direction F, ((usingTuples P a d).card - 1) = κ := by
  have hrestrict :
      (∑ d : Direction F, ((usingTuples P a d).card - 1)) =
        ∑ d ∈ usedDirections a, ((usingTuples P a d).card - 1) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro d _ hd
    simp [usingTuples_eq_empty_of_not_used P a d hd]
  rw [hrestrict, usedDirections, Finset.sum_image]
  · simp_rw [usingTuples_class_card P a ha]
    exact sum_class_excess P hκ
  · intro c _ e _ hce
    exact ha hce

omit [Fintype F] in
@[simp] theorem mem_tuplePoints (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (M : MergedPairs F)
    (i : Fin b) (x : Point F) :
    x ∈ tuplePoints P a bits M i ↔ ∃ j, prescribedPoint P a bits M (i, j) = x := by
  simp [tuplePoints]

omit [Fintype F] in
theorem prescribedDesignated_eq_biUnion (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (M : MergedPairs F) :
    prescribedDesignated P a bits M = Finset.univ.biUnion (tuplePoints P a bits M) := by
  ext x
  simp only [prescribedDesignated, Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_biUnion, mem_tuplePoints]
  exact ⟨fun ⟨⟨i,j⟩, h⟩ => ⟨i, j, h⟩,
    fun ⟨i, j, h⟩ => ⟨(i,j), h⟩⟩

theorem prescribedDesignated_card (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (M : MergedPairs F) (hadm : Admissible P a bits p M) :
    (prescribedDesignated P a bits M).card = 4 * b := by
  rw [prescribedDesignated, Finset.card_image_of_injective _ hadm.2.1]
  simp [Nat.mul_comm]

theorem tuplePoints_subset_target (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (M : MergedPairs F) (hal : Aligned P a bits p M) (i : Fin b) :
    tuplePoints P a bits M i ⊆ linePoints (lineThrough (a.1 i) p) := by
  intro x hx
  obtain ⟨j, rfl⟩ := (mem_tuplePoints P a bits M i x).mp hx
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hal (i,j)⟩

theorem tuplePoints_inter_merged_card_le_two (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (M : MergedPairs F) (hadm : Admissible P a bits p M)
    (i : Fin b) (d : Direction F) :
    (tuplePoints P a bits M i ∩ mergedPoints M d).card ≤ 2 := by
  have hne (s : Bool) : lineThrough (a.1 i) p ≠ constituent M d s := by
    intro he
    apply hadm.2.2.2.1 i
    rw [he]
    exact Finset.mem_image.mpr ⟨(d,s), Finset.mem_univ _, rfl⟩
  have hone (s : Bool) :
      (tuplePoints P a bits M i ∩ linePoints (constituent M d s)).card ≤ 1 := by
    apply (Finset.card_le_card ?_).trans
      (linePoints_inter_card_le_one _ _ (hne s))
    exact Finset.inter_subset_inter_right
      (tuplePoints_subset_target P a bits p M hadm.1 i)
  rw [mergedPoints, Finset.inter_union_distrib_left]
  exact (Finset.card_union_le _ _).trans (by have h0 := hone false; have h1 := hone true; omega)

def Precoverage (P : EqualityPattern b κ) (a : DirectionAssignment F b κ)
    (bits : Bits b) (p : Point F) (M : MergedPairs F) : Prop :=
  (prescribedPartners P a bits p M).Nonempty

def UsedPairExtra (P : EqualityPattern b κ) (a : DirectionAssignment F b κ)
    (bits : Bits b) (M : MergedPairs F) : Prop :=
  ∃ d ∈ usedDirections a, ∃ i, i ∉ usingTuples P a d ∧
    ∃ x ∈ tuplePoints P a bits M i, x ∈ mergedPoints M d

def ForbiddenCollinearTriple (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (M : MergedPairs F) : Prop :=
  ∃ l : Line F, (∀ i, l ≠ lineThrough (a.1 i) p) ∧
    (∀ c s, l ≠ constituent M (a.2 c) s) ∧
    3 ≤ (prescribedDesignated P a bits M ∩ linePoints l).card

def UnusedNoncollinearTriple (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (M : MergedPairs F) : Prop :=
  ∃ d, d ∉ usedDirections a ∧ ∃ U : Finset (Point F), U.card = 3 ∧
    U ⊆ prescribedDesignated P a bits M ∩ mergedPoints M d ∧
    ¬ ∃ l : Line F, U ⊆ linePoints l

theorem line_inter_merged_card_le_two (M : MergedPairs F) (d : Direction F)
    (l : Line F) (hne : ∀ s, l ≠ constituent M d s) :
    (linePoints l ∩ mergedPoints M d).card ≤ 2 := by
  rw [mergedPoints, Finset.inter_union_distrib_left]
  exact (Finset.card_union_le _ _).trans (by
    have h0 := linePoints_inter_card_le_one l _ (hne false)
    have h1 := linePoints_inter_card_le_one l _ (hne true)
    omega)

theorem used_pair_trace_le (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (M : MergedPairs F) (hadm : Admissible P a bits p M)
    (hno : ¬ UsedPairExtra P a bits M) (d : Direction F)
    (hd : d ∈ usedDirections a) :
    (prescribedDesignated P a bits M ∩ mergedPoints M d).card ≤
      2 * (usingTuples P a d).card := by
  have hsub : prescribedDesignated P a bits M ∩ mergedPoints M d ⊆
      (usingTuples P a d).biUnion (fun i =>
        tuplePoints P a bits M i ∩ mergedPoints M d) := by
    intro x hx
    obtain ⟨⟨i,j⟩, _, hpoint⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hx).1
    have hxt : x ∈ tuplePoints P a bits M i :=
      (mem_tuplePoints P a bits M i x).mpr ⟨j, hpoint⟩
    have hi : i ∈ usingTuples P a d := by
      by_contra hn
      exact hno ⟨d, hd, i, hn, x, hxt, (Finset.mem_inter.mp hx).2⟩
    exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_inter.mpr
      ⟨hxt, (Finset.mem_inter.mp hx).2⟩⟩
  exact (Finset.card_le_card hsub).trans (by
    have h := Finset.card_biUnion_le_card_mul (usingTuples P a d)
      (fun i => tuplePoints P a bits M i ∩ mergedPoints M d) 2
      (fun i _ => tuplePoints_inter_merged_card_le_two P a bits p M hadm i d)
    simpa [Nat.mul_comm] using h)

theorem unused_pair_trace_le (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (M : MergedPairs F) (hadm : Admissible P a bits p M)
    (hcol : ¬ ForbiddenCollinearTriple P a bits p M)
    (hnoncol : ¬ UnusedNoncollinearTriple P a bits M)
    (d : Direction F) (hd : d ∉ usedDirections a) :
    (prescribedDesignated P a bits M ∩ mergedPoints M d).card ≤ 2 := by
  by_contra hbig
  have hthree : 3 ≤ (prescribedDesignated P a bits M ∩ mergedPoints M d).card := by omega
  obtain ⟨U, hU, hcard⟩ := Finset.exists_subset_card_eq hthree
  have hline : ∃ l : Line F, U ⊆ linePoints l := by
    by_contra hn
    exact hnoncol ⟨d, hd, U, hcard, hU, hn⟩
  obtain ⟨l, hl⟩ := hline
  have htrace : 3 ≤ (prescribedDesignated P a bits M ∩ linePoints l).card := by
    rw [← hcard]
    apply Finset.card_le_card
    intro x hx
    exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp (hU hx)).1, hl hx⟩
  have heq : ∃ s, l = constituent M d s := by
    by_contra hn
    have hne : ∀ s, l ≠ constituent M d s := by simpa using hn
    have hle := line_inter_merged_card_le_two M d l hne
    have hcap : U.card ≤ (linePoints l ∩ mergedPoints M d).card := by
      apply Finset.card_le_card
      intro x hx
      exact Finset.mem_inter.mpr ⟨hl hx, (Finset.mem_inter.mp (hU hx)).2⟩
    omega
  obtain ⟨s, rfl⟩ := heq
  apply hcol
  refine ⟨constituent M d s, ?_, ?_, htrace⟩
  · intro i he
    apply hadm.2.2.2.1 i
    rw [← he]
    exact Finset.mem_image.mpr ⟨(d,s), Finset.mem_univ _, rfl⟩
  · intro c t he
    apply hd
    exact Finset.mem_image.mpr ⟨c, Finset.mem_univ _,
      (congrArg Prod.fst he).symm⟩

def UnusedPrecoverage (P : EqualityPattern b κ) (a : DirectionAssignment F b κ)
    (bits : Bits b) (p : Point F) (M : MergedPairs F) : Prop :=
  ∃ d, d ∉ usedDirections a ∧ ∃ s, OnLine p (constituent M d s) ∧
    ∃ x ∈ prescribedDesignated P a bits M, OnLine x (constituent M d (!s))

theorem precoverage_iff_unused (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (M : MergedPairs F) (ha : Eligible P a) (hadm : Admissible P a bits p M) :
    Precoverage P a bits p M ↔ UnusedPrecoverage P a bits p M := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨hF, ⟨d,s⟩, hd, hp, hpoint⟩ :=
      (PrescribedGeometry.mem_prescribedPartners_iff_unused ha hadm x).mp hx
    exact ⟨d, hd, s, hp, x, hF, hpoint⟩
  · rintro ⟨d, hd, s, hp, x, hF, hpoint⟩
    exact ⟨x, (PrescribedGeometry.mem_prescribedPartners_iff_unused ha hadm x).mpr
      ⟨hF, (d,s), hd, hp, hpoint⟩⟩

def extraCapacity (P : EqualityPattern b κ) (a : DirectionAssignment F b κ) :
    LocalPiece F → ℕ
  | Sum.inr (Sum.inr d) => 2 * ((usingTuples P a d).card - 1)
  | _ => 0

omit [Field F] in
theorem sum_extraCapacity (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (ha : Function.Injective a.2)
    (hκ : κ ≤ 4 * b) :
    ∑ x : LocalPiece F, extraCapacity P a x = 2 * κ := by
  simp only [Fintype.sum_sum_type, extraCapacity, Finset.sum_const_zero, zero_add]
  rw [← Finset.mul_sum, sum_direction_excess P a ha hκ]

theorem allowed_piece_trace_le (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (M : MergedPairs F) (ha : Eligible P a) (hadm : Admissible P a bits p M)
    (hused : ¬ UsedPairExtra P a bits M)
    (hcol : ¬ ForbiddenCollinearTriple P a bits p M)
    (hnoncol : ¬ UnusedNoncollinearTriple P a bits M)
    (x : LocalPiece F) (hx : AllowedPiece a p M x) :
    (prescribedDesignated P a bits M ∩ piecePoints M x).card ≤
      2 + extraCapacity P a x := by
  rcases x with U | l | d
  · exact (Finset.card_le_card Finset.inter_subset_right).trans hx
  · change (prescribedDesignated P a bits M ∩ linePoints l).card ≤ 2
    by_contra hbig
    apply hcol
    refine ⟨l, ?_, ?_, by omega⟩
    · intro i he
      apply hx
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, he.symm⟩
    · intro c s he
      apply hx
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨(a.2 c,s), Finset.mem_univ _, he.symm⟩
  · change (prescribedDesignated P a bits M ∩ mergedPoints M d).card ≤
      2 + 2 * ((usingTuples P a d).card - 1)
    by_cases hd : d ∈ usedDirections a
    · have hle := used_pair_trace_le P a bits p M hadm hused d hd
      obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hd
      have hpos : 0 < (usingTuples P a (a.2 c)).card := by
        rw [usingTuples_class_card P a ha.2.1]
        exact classUseCount_pos P c
      omega
    · have hle := unused_pair_trace_le P a bits p M hadm hcol hnoncol d hd
      omega

theorem cover_budget_le (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (M : MergedPairs F) (ha : Eligible P a) (hadm : Admissible P a bits p M)
    (hκ : κ ≤ 4 * b) (hcover : BadCover P a bits p M)
    (hpre : ¬ Precoverage P a bits p M) (hused : ¬ UsedPairExtra P a bits M)
    (hcol : ¬ ForbiddenCollinearTriple P a bits p M)
    (hnoncol : ¬ UnusedNoncollinearTriple P a bits M) :
    4 * b ≤ 2 * (b - 1) + 2 * κ := by
  obtain ⟨A, hA, hallowed, hcover⟩ := hcover
  have hsub : prescribedDesignated P a bits M ⊆
      A.biUnion (fun x => prescribedDesignated P a bits M ∩ piecePoints M x) := by
    intro y hy
    rcases Finset.mem_union.mp (hcover hy) with hp | hp
    · exact False.elim (hpre ⟨y, hp⟩)
    · obtain ⟨x, hx, hyx⟩ := Finset.mem_biUnion.mp hp
      exact Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_inter.mpr ⟨hy, hyx⟩⟩
  have hbonus : (∑ x ∈ A, extraCapacity P a x) ≤ 2 * κ := by
    rw [← sum_extraCapacity P a ha.2.1 hκ]
    exact Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
  calc
    4 * b = (prescribedDesignated P a bits M).card :=
      (prescribedDesignated_card P a bits p M hadm).symm
    _ ≤ ∑ x ∈ A, (prescribedDesignated P a bits M ∩ piecePoints M x).card :=
      (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    _ ≤ ∑ x ∈ A, (2 + extraCapacity P a x) := by
      apply Finset.sum_le_sum
      intro x hx
      exact allowed_piece_trace_le P a bits p M ha hadm hused hcol hnoncol x (hallowed x hx)
    _ = 2 * A.card + ∑ x ∈ A, extraCapacity P a x := by
      rw [Finset.sum_add_distrib]
      simp [Nat.mul_comm]
    _ ≤ 2 * A.card + 2 * κ := Nat.add_le_add_left hbonus _
    _ ≤ 2 * (b - 1) + 2 * κ := by omega

theorem admissibleBadCover_four_events (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (M : MergedPairs F) (hb : 3 ≤ b) (hκ : κ ≤ 2)
    (ha : Eligible P a) (hbad : AdmissibleBadCover P a bits p M) :
    UnusedPrecoverage P a bits p M ∨ UsedPairExtra P a bits M ∨
      ForbiddenCollinearTriple P a bits p M ∨ UnusedNoncollinearTriple P a bits M := by
  by_contra hnone
  push Not at hnone
  have hpre : ¬ Precoverage P a bits p M := by
    intro hp
    exact hnone.1 ((precoverage_iff_unused P a bits p M ha hbad.1).mp hp)
  have hbound := cover_budget_le P a bits p M ha hbad.1 (by omega) hbad.2
    hpre hnone.2.1 hnone.2.2.1 hnone.2.2.2
  omega

end
end Balanced.Local.FourEvents

end OAI
