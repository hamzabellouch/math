import OAI.Combinatorics.BalancedRyser.Local.ChildAlignment

namespace OAI

namespace Balanced.PartialAlignment
open TupleAlignment

variable {F : Type*}

abbrev PartialOffsets (J : Finset (Fin 4)) (a : Fin 4 → Bool → F) :=
  {o : Fin 4 → Bool → F // ∀ i ∈ J, o i = a i}

def freshGenerators (J : Finset (Fin 4)) : Finset (Fin 4) :=
  Finset.univ.filter (fun i => i ∉ J)

def freePositions (J : Finset (Fin 4)) : Finset (Fin 4) :=
  Finset.univ.filter (fun i => i ∉ J ∧ i + 1 ∉ J)

def fixedPositions (J : Finset (Fin 4)) : Finset (Fin 4) :=
  Finset.univ.filter (fun i => i ∈ J ∧ i + 1 ∈ J)

def partialFreshEquiv (J : Finset (Fin 4)) (a : Fin 4 → Bool → F) :
    PartialOffsets J a ≃ ({i : Fin 4 // i ∉ J} → Bool → F) where
  toFun o i := o.1 i.1
  invFun f := ⟨fun i => if hi : i ∈ J then a i else f ⟨i,hi⟩, by
    intro i hi
    simp [hi]⟩
  left_inv o := by
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ J
    · simp only [dite_eq_left hi]
      exact (o.2 i hi).symm
    · simp only [dite_eq_right hi]
  right_inv f := by
    funext i
    simp only [dite_eq_right i.2]

theorem alignment_exponent_identity (J : Finset (Fin 4)) :
    (freePositions J).card + (4 - (fixedPositions J).card) =
      2 * (freshGenerators J).card := by
  have h : ∀ J : Finset (Fin 4),
      (freePositions J).card + (4 - (fixedPositions J).card) =
        2 * (freshGenerators J).card := by decide
  exact h J

variable [Field F]

abbrev AlignedPartialOffsets (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (c : F) (J : Finset (Fin 4)) (a : Fin 4 → Bool → F) :=
  {o : PartialOffsets J a // ∀ i,
    OnLine (tuplePositionEquiv d hd σ o.1 i) (g,c)}

def alignedFreeCoordinates (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (c : F) (J : Finset (Fin 4)) (a : Fin 4 → Bool → F)
    (o : AlignedPartialOffsets d hd σ g c J a) :
    {i : Fin 4 // i ∈ freePositions J} → F :=
  fun i => (linePointEquiv g c) ⟨tuplePositionEquiv d hd σ o.1.1 i.1, o.2 i.1⟩

theorem alignedFreeCoordinates_injective (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (hg : ∀ i, d i ≠ g) (c : F)
    (J : Finset (Fin 4)) (a : Fin 4 → Bool → F) :
    Function.Injective (alignedFreeCoordinates d hd σ g c J a) := by
  intro o p h
  apply Subtype.ext
  apply Subtype.ext
  apply (tuplePositionEquiv d hd σ).injective
  funext i
  by_cases hfree : i ∉ J ∧ i + 1 ∉ J
  · have hi : i ∈ freePositions J := by simp [freePositions, hfree]
    have hcoord := congrFun h (⟨i,hi⟩ : {i // i ∈ freePositions J})
    exact congrArg Subtype.val ((linePointEquiv g c).injective hcoord)
  · by_cases hi : i ∈ J
    · apply (lineEvalEquiv (d i) g (hg i)).injective
      apply Prod.ext
      · change lineEval (d i) (tuplePositionEquiv d hd σ o.1.1 i) =
          lineEval (d i) (tuplePositionEquiv d hd σ p.1.1 i)
        rw [tuplePosition_lineEval_left, tuplePosition_lineEval_left,
          o.1.2 i hi, p.1.2 i hi]
      · exact (o.2 i).trans (p.2 i).symm
    · have hnext : i + 1 ∈ J := by tauto
      apply (lineEvalEquiv (d (i + 1)) g (hg (i + 1))).injective
      apply Prod.ext
      · change lineEval (d (i + 1)) (tuplePositionEquiv d hd σ o.1.1 i) =
          lineEval (d (i + 1)) (tuplePositionEquiv d hd σ p.1.1 i)
        rw [tuplePosition_lineEval_right, tuplePosition_lineEval_right,
          o.1.2 (i + 1) hnext, p.1.2 (i + 1) hnext]
      · exact (o.2 i).trans (p.2 i).symm

instance (J : Finset (Fin 4)) (a : Fin 4 → Bool → F) :
    Nonempty (PartialOffsets J a) := ⟨⟨a, by intro i hi; rfl⟩⟩

section Finite
variable [Fintype F] [DecidableEq F]

omit [Field F] in
theorem card_partialOffsets (J : Finset (Fin 4)) (a : Fin 4 → Bool → F) :
    Fintype.card (PartialOffsets J a) =
      Fintype.card F ^ (2 * (freshGenerators J).card) := by
  rw [Fintype.card_congr (partialFreshEquiv J a)]
  simp only [Fintype.card_fun, Fintype.card_bool, ← pow_mul, Fintype.card_subtype]
  rfl

theorem card_alignedPartialOffsets_le (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (hg : ∀ i, d i ≠ g) (c : F)
    (J : Finset (Fin 4)) (a : Fin 4 → Bool → F) :
    Fintype.card (AlignedPartialOffsets d hd σ g c J a) ≤
      Fintype.card F ^ (freePositions J).card := by
  calc
    Fintype.card (AlignedPartialOffsets d hd σ g c J a) ≤
        Fintype.card ({i : Fin 4 // i ∈ freePositions J} → F) :=
      Fintype.card_le_of_injective _
        (alignedFreeCoordinates_injective d hd σ g hg c J a)
    _ = _ := by simp

theorem partial_alignment_probability_le (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (hg : ∀ i, d i ≠ g) (c : F)
    (J : Finset (Fin 4)) (a : Fin 4 → Bool → F) :
    ((PMF.uniformOfFintype (PartialOffsets J a)).toOuterMeasure
      {o | ∀ i, OnLine (tuplePositionEquiv d hd σ o.1 i) (g,c)}).toReal ≤
      (Fintype.card F : ℝ)⁻¹ ^ (4 - (fixedPositions J).card) := by
  rw [PMF.toOuterMeasure_uniformOfFintype_apply, ENNReal.toReal_div]
  simp only [ENNReal.toReal_natCast]
  change (Fintype.card (AlignedPartialOffsets d hd σ g c J a) : ℝ) /
    (Fintype.card (PartialOffsets J a) : ℝ) ≤ _
  rw [card_partialOffsets, Nat.cast_pow]
  have hcard : (Fintype.card (AlignedPartialOffsets d hd σ g c J a) : ℝ) ≤
      (Fintype.card F : ℝ) ^ (freePositions J).card := by
    exact_mod_cast card_alignedPartialOffsets_le d hd σ g hg c J a
  have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  calc
    (Fintype.card (AlignedPartialOffsets d hd σ g c J a) : ℝ) /
        (Fintype.card F : ℝ) ^ (2 * (freshGenerators J).card) ≤
      (Fintype.card F : ℝ) ^ (freePositions J).card /
        (Fintype.card F : ℝ) ^ (2 * (freshGenerators J).card) :=
      div_le_div_of_nonneg_right hcard (by positivity)
    _ = _ := by
      rw [← alignment_exponent_identity J, pow_add, div_mul_eq_div_div,
        div_self (pow_ne_zero _ hq), one_div, inv_pow]

omit [DecidableEq F] in

theorem partialOffsets_supported (J : Finset (Fin 4)) (a : Fin 4 → Bool → F) :
    ∃ o ∈ {o : Fin 4 → Bool → F | ∀ i ∈ J, o i = a i},
      o ∈ (PMF.uniformOfFintype (Fin 4 → Bool → F)).support :=
  ⟨a, by intro i hi; rfl, PMF.mem_support_uniformOfFintype _⟩

theorem partialOffsets_conditional_law (J : Finset (Fin 4)) (a : Fin 4 → Bool → F) :
    (PMF.uniformOfFintype (Fin 4 → Bool → F)).filter
      {o | ∀ i ∈ J, o i = a i} (partialOffsets_supported J a) =
      (PMF.uniformOfFintype (PartialOffsets J a)).map Subtype.val := by
  let : Nonempty ({o : Fin 4 → Bool → F | ∀ i ∈ J, o i = a i} :
      Set (Fin 4 → Bool → F)) := ⟨⟨a, by intro i hi; rfl⟩⟩
  exact Balanced.uniform_filter_eq_subtype_map _ _

theorem original_conditional_alignment_probability_le (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (hg : ∀ i, d i ≠ g) (c : F)
    (J : Finset (Fin 4)) (a : Fin 4 → Bool → F) :
    (((PMF.uniformOfFintype (Fin 4 → Bool → F)).filter
      {o | ∀ i ∈ J, o i = a i} (partialOffsets_supported J a)).toOuterMeasure
      {o | ∀ i, OnLine (tuplePositionEquiv d hd σ o i) (g,c)}).toReal ≤
      (Fintype.card F : ℝ)⁻¹ ^ (4 - (fixedPositions J).card) := by
  rw [partialOffsets_conditional_law, PMF.toOuterMeasure_map_apply]
  exact partial_alignment_probability_le d hd σ g hg c J a

end Finite
end Balanced.PartialAlignment

end OAI
