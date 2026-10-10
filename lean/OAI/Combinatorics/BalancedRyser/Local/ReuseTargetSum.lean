import OAI.Combinatorics.BalancedRyser.Local.PartialAlignment
import OAI.Combinatorics.BalancedRyser.Local.ReuseExtensionArithmetic
import OAI.Combinatorics.BalancedRyser.Local.ReuseTargetDirections

namespace OAI

namespace Balanced.PartialAlignment
open TupleAlignment

noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def externalAlignmentEvent (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (p : Point F) (g : Direction F) (J : Finset (Fin 4))
    (a : Fin 4 → Bool → F) : Set (PartialOffsets J a) :=
  {o | (∀ i, OnLine (tuplePositionEquiv d hd σ o.1 i) (lineThrough g p)) ∧
    ∀ i, tuplePositionEquiv d hd σ o.1 i ≠ p}

def externalAlignmentProbability (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (p : Point F) (g : Direction F) (J : Finset (Fin 4))
    (a : Fin 4 → Bool → F) : ℝ :=
  ((PMF.uniformOfFintype (PartialOffsets J a)).toOuterMeasure
    (externalAlignmentEvent d hd σ p g J a)).toReal

theorem externalAlignmentProbability_le (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (p : Point F) (g : Direction F) (hg : ∀ i, d i ≠ g)
    (J : Finset (Fin 4)) (a : Fin 4 → Bool → F) :
    externalAlignmentProbability d hd σ p g J a ≤
      (Fintype.card F : ℝ)⁻¹ ^ (4 - (fixedPositions J).card) := by
  apply le_trans ?_ (partial_alignment_probability_le d hd σ g hg (lineEval g p) J a)
  unfold externalAlignmentProbability
  rw [PMF.toOuterMeasure_uniformOfFintype_apply,
    PMF.toOuterMeasure_uniformOfFintype_apply, ENNReal.toReal_div, ENNReal.toReal_div]
  simp only [ENNReal.toReal_natCast]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Fintype.card_le_of_injective
    (fun o : externalAlignmentEvent d hd σ p g J a =>
      (⟨o.1, o.2.1⟩ : AlignedPartialOffsets d hd σ g (lineEval g p) J a))
    (by
      intro o r h
      apply Subtype.ext
      exact congrArg (fun z : AlignedPartialOffsets d hd σ g (lineEval g p) J a => z.1) h)

omit [Fintype F] [DecidableEq F] in
theorem tuplePosition_fixed (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (J : Finset (Fin 4)) (a : Fin 4 → Bool → F)
    (o : PartialOffsets J a) (i : Fin 4) (hi : i ∈ fixedPositions J) :
    tuplePositionEquiv d hd σ o.1 i = tuplePositionEquiv d hd σ a i := by
  obtain ⟨_, hi, hnext⟩ := Finset.mem_filter.mp hi
  simp only [tuplePositionEquiv_apply, o.2 i hi, o.2 (i + 1) hnext]

def possibleExternalTargets (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (p : Point F) (J : Finset (Fin 4)) (a : Fin 4 → Bool → F) :
    Finset (Direction F) :=
  Finset.univ.filter (fun g => ∃ o, o ∈ externalAlignmentEvent d hd σ p g J a)

theorem card_possibleExternalTargets_le_one (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (p : Point F) (J : Finset (Fin 4)) (a : Fin 4 → Bool → F)
    (hfixed : (fixedPositions J).Nonempty) :
    (possibleExternalTargets d hd σ p J a).card ≤ 1 := by
  obtain ⟨i, hi⟩ := hfixed
  apply Finset.card_le_one.mpr
  intro g hg h hh
  obtain ⟨o, ho⟩ := (Finset.mem_filter.mp hg).2
  obtain ⟨r, hr⟩ := (Finset.mem_filter.mp hh).2
  have haway := ho.2 i
  have hon := ho.1 i
  have hother := hr.1 i
  rw [tuplePosition_fixed d hd σ J a o i hi] at haway hon
  rw [tuplePosition_fixed d hd σ J a r i hi] at hother
  exact direction_eq_of_common_point p _ haway.symm g h hon hother

theorem externalAlignmentProbability_eq_zero_of_not_possible
    (d : Fin 4 → Direction F) (hd : ∀ i, d i ≠ d (i + 1))
    (σ : Fin 4 → Bool) (p : Point F) (g : Direction F)
    (J : Finset (Fin 4)) (a : Fin 4 → Bool → F)
    (hg : g ∉ possibleExternalTargets d hd σ p J a) :
    externalAlignmentProbability d hd σ p g J a = 0 := by
  have hempty : externalAlignmentEvent d hd σ p g J a = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro o ho
    exact hg (Finset.mem_filter.mpr ⟨Finset.mem_univ _, o, ho⟩)
  simp [externalAlignmentProbability, hempty]

theorem sum_externalAlignmentProbability_le
    (d : Fin 4 → Direction F) (hd : ∀ i, d i ≠ d (i + 1))
    (σ : Fin 4 → Bool) (p : Point F) (J : Finset (Fin 4))
    (a : Fin 4 → Bool → F) :
    (∑ g ∈ (Finset.univ.filter (fun g : Direction F => ∀ i, d i ≠ g)),
      externalAlignmentProbability d hd σ p g J a) ≤
      (if (fixedPositions J).card = 0 then (Fintype.card F : ℝ) + 1 else 1) *
        ((Fintype.card F : ℝ)⁻¹ ^ (4 - (fixedPositions J).card)) := by
  let eligible := Finset.univ.filter (fun g : Direction F => ∀ i, d i ≠ g)
  let possible := possibleExternalTargets d hd σ p J a
  have hsum : (∑ g ∈ eligible ∩ possible, externalAlignmentProbability d hd σ p g J a) =
      ∑ g ∈ eligible, externalAlignmentProbability d hd σ p g J a := by
    apply Finset.sum_subset Finset.inter_subset_left
    intro g hg hnot
    apply externalAlignmentProbability_eq_zero_of_not_possible
    intro hp
    exact hnot (Finset.mem_inter.mpr ⟨hg, hp⟩)
  rw [← hsum]
  calc
    (∑ g ∈ eligible ∩ possible, externalAlignmentProbability d hd σ p g J a) ≤
        ((eligible ∩ possible).card : ℝ) *
          ((Fintype.card F : ℝ)⁻¹ ^ (4 - (fixedPositions J).card)) := by
      simpa only [nsmul_eq_mul] using Finset.sum_le_card_nsmul (eligible ∩ possible)
        (fun g => externalAlignmentProbability d hd σ p g J a) _
        (fun g hg => externalAlignmentProbability_le d hd σ p g
          (Finset.mem_filter.mp (Finset.mem_inter.mp hg).1).2 J a)
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      split_ifs with hzero
      · have hc := Finset.card_le_univ (eligible ∩ possible)
        simpa only [Direction, Fintype.card_option, Nat.cast_add, Nat.cast_one] using
          (Nat.cast_le.mpr hc : ((eligible ∩ possible).card : ℝ) ≤ _)
      · have hc := (Finset.card_le_card (Finset.inter_subset_right :
            eligible ∩ possible ⊆ possible)).trans
          (card_possibleExternalTargets_le_one d hd σ p J a
            (Finset.card_pos.mp (Nat.pos_of_ne_zero hzero)))
        exact_mod_cast hc

theorem fixedPositions_eq_fixedGeneratorPositions (J : Finset (Fin 4)) :
    fixedPositions J = fixedGeneratorPositions J := by
  ext i
  simp [fixedPositions, fixedGeneratorPositions]

theorem scaled_sum_externalAlignmentProbability_le
    (d : Fin 4 → Direction F) (hd : ∀ i, d i ≠ d (i + 1))
    (σ : Fin 4 → Bool) (p : Point F) (J : Finset (Fin 4))
    (a : Fin 4 → Bool → F) (K : ℝ) (hK : 0 ≤ K) :
    (Fintype.card F : ℝ) ^ (4 - J.card) *
      (∑ g ∈ (Finset.univ.filter (fun g : Direction F => ∀ i, d i ≠ g)),
        externalAlignmentProbability d hd σ p g J a) * (K / Fintype.card F) ≤
      2 * K / (Fintype.card F : ℝ) ^ reuseSaving J.card := by
  let q : ℝ := Fintype.card F
  have hq : 1 ≤ q := by
    change (1 : ℝ) ≤ (Fintype.card F : ℝ)
    exact_mod_cast (show 1 ≤ Fintype.card F from Fintype.card_pos)
  have hsum := sum_externalAlignmentProbability_le d hd σ p J a
  rw [fixedPositions_eq_fixedGeneratorPositions] at hsum
  have htarget :
      (if (fixedGeneratorPositions J).card = 0 then q + 1 else 1) ≤
        2 * (if (fixedGeneratorPositions J).card = 0 then q else 1) := by
    split_ifs <;> linarith
  calc
    q ^ (4 - J.card) *
        (∑ g ∈ (Finset.univ.filter (fun g : Direction F => ∀ i, d i ≠ g)),
          externalAlignmentProbability d hd σ p g J a) * (K / q) ≤
      q ^ (4 - J.card) *
        ((if (fixedGeneratorPositions J).card = 0 then q + 1 else 1) *
          (q⁻¹ ^ (4 - (fixedGeneratorPositions J).card))) * (K / q) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ q ^ (4 - J.card) *
        (2 * (if (fixedGeneratorPositions J).card = 0 then q else 1) *
          (q⁻¹ ^ (4 - (fixedGeneratorPositions J).card))) * (K / q) := by
      gcongr
    _ = (2 * K) * (q ^ (4 - J.card) *
        (if (fixedGeneratorPositions J).card = 0 then q else 1) /
        q ^ (4 - (fixedGeneratorPositions J).card) / q) := by
      simp only [inv_pow, div_eq_mul_inv]
      ring
    _ ≤ 2 * K / q ^ reuseSaving J.card :=
      reuse_extension_scale_mul_le q (2 * K) hq (by positivity) J

end
end Balanced.PartialAlignment

end OAI
