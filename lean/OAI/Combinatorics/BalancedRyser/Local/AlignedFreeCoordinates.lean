import OAI.Combinatorics.BalancedRyser.Local.AlignedListProbability

namespace OAI

namespace Balanced.AlignedListProbability

open TupleAlignment PartialAlignment
noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem card_alignedPartialOffsets_eq (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (hg : ∀ i, d i ≠ g) (c : F)
    (J : Finset (Fin 4)) (hJ : J.card ≤ 1) (a : Fin 4 → Bool → F) :
    Fintype.card (AlignedPartialOffsets d hd σ g c J a) =
      Fintype.card F ^ (freePositions J).card := by
  have hp := partial_alignment_probability_eq d hd σ g hg c J hJ a
  rw [PMF.toOuterMeasure_uniformOfFintype_apply, ENNReal.toReal_div] at hp
  simp only [ENNReal.toReal_natCast] at hp
  change (Fintype.card (AlignedPartialOffsets d hd σ g c J a) : ℝ) /
    Fintype.card (PartialOffsets J a) = (Fintype.card F : ℝ)⁻¹ ^ 4 at hp
  rw [card_partialOffsets, Nat.cast_pow] at hp
  have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hc := (div_eq_iff (pow_ne_zero _ hq)).mp hp
  have hcycle : (freePositions J).card + 4 = 2 * (freshGenerators J).card := by
    have h : ∀ K : Finset (Fin 4), K.card ≤ 1 →
        (freePositions K).card + 4 = 2 * (freshGenerators K).card := by decide
    exact h J hJ
  have hr : (Fintype.card (AlignedPartialOffsets d hd σ g c J a) : ℝ) =
      (Fintype.card F : ℝ) ^ (freePositions J).card := by
    rw [hc, ← hcycle, pow_add]
    calc
      _ = (Fintype.card F : ℝ) ^ (freePositions J).card *
          ((Fintype.card F : ℝ)⁻¹ ^ 4 * (Fintype.card F : ℝ) ^ 4) := by ring
      _ = _ := by rw [← mul_pow, inv_mul_cancel₀ hq, one_pow, mul_one]
  exact_mod_cast hr

def alignedFreeCoordinatesEquiv (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (hg : ∀ i, d i ≠ g) (c : F)
    (J : Finset (Fin 4)) (hJ : J.card ≤ 1) (a : Fin 4 → Bool → F) :
    AlignedPartialOffsets d hd σ g c J a ≃ ({i : Fin 4 // i ∈ freePositions J} → F) :=
  Equiv.ofBijective (alignedFreeCoordinates d hd σ g c J a)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨alignedFreeCoordinates_injective d hd σ g hg c J a, by
        rw [card_alignedPartialOffsets_eq d hd σ g hg c J hJ a]
        simp⟩)

theorem card_freePositions_of_small (J : Finset (Fin 4)) (hJ : J.card ≤ 1) :
    (freePositions J).card = 4 - 2 * J.card := by
  have h : ∀ K : Finset (Fin 4), K.card ≤ 1 →
      (freePositions K).card = 4 - 2 * K.card := by decide
  exact h J hJ

theorem alignedPartial_supported (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (hg : ∀ i, d i ≠ g) (c : F)
    (J : Finset (Fin 4)) (hJ : J.card ≤ 1) (a : Fin 4 → Bool → F) :
    ∃ o ∈ {o : PartialOffsets J a | ∀ i,
      OnLine (tuplePositionEquiv d hd σ o.1 i) (g,c)},
      o ∈ (PMF.uniformOfFintype (PartialOffsets J a)).support := by
  let o := (alignedFreeCoordinatesEquiv d hd σ g hg c J hJ a).symm (fun _ => 0)
  exact ⟨o.1, o.2, PMF.mem_support_uniformOfFintype _⟩

theorem alignedPartial_conditional_law (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (hg : ∀ i, d i ≠ g) (c : F)
    (J : Finset (Fin 4)) (hJ : J.card ≤ 1) (a : Fin 4 → Bool → F) :
    (PMF.uniformOfFintype (PartialOffsets J a)).filter
      {o | ∀ i, OnLine (tuplePositionEquiv d hd σ o.1 i) (g,c)}
      (alignedPartial_supported d hd σ g hg c J hJ a) =
    (PMF.uniformOfFintype ({i : Fin 4 // i ∈ freePositions J} → F)).map
      (fun x => ((alignedFreeCoordinatesEquiv d hd σ g hg c J hJ a).symm x).1) := by
  let e := alignedFreeCoordinatesEquiv d hd σ g hg c J hJ a
  let : Nonempty (AlignedPartialOffsets d hd σ g c J a) := ⟨e.symm (fun _ => 0)⟩
  let : Nonempty ({o : PartialOffsets J a | ∀ i,
      OnLine (tuplePositionEquiv d hd σ o.1 i) (g,c)} : Set (PartialOffsets J a)) :=
    ⟨e.symm (fun _ => 0)⟩
  rw [Balanced.uniform_filter_eq_subtype_map]
  change (PMF.uniformOfFintype (AlignedPartialOffsets d hd σ g c J a)).map Subtype.val = _
  have h := uniform_map_equiv e.symm
  rw [← h, PMF.map_comp]
  rfl

theorem alignedPartial_generated_free (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (hg : ∀ i, d i ≠ g) (c : F)
    (J : Finset (Fin 4)) (hJ : J.card ≤ 1) (a : Fin 4 → Bool → F)
    (x : {i : Fin 4 // i ∈ freePositions J} → F) (i : {i : Fin 4 // i ∈ freePositions J}) :
    tuplePositionEquiv d hd σ
      ((alignedFreeCoordinatesEquiv d hd σ g hg c J hJ a).symm x).1.1 i.1 =
        ((linePointEquiv g c).symm (x i)).1 := by
  let e := alignedFreeCoordinatesEquiv d hd σ g hg c J hJ a
  have h := congrFun (e.apply_symm_apply x) i
  change (linePointEquiv g c) ⟨tuplePositionEquiv d hd σ
      (e.symm x).1.1 i.1, (e.symm x).2 i.1⟩ = x i at h
  have hp := congrArg (fun y => ((linePointEquiv g c).symm y).1) h
  simpa only [Equiv.symm_apply_apply] using hp

omit [Fintype F] [DecidableEq F] in

theorem alignedPartial_position_old_left (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (hg : ∀ i, d i ≠ g) (c : F)
    (J : Finset (Fin 4)) (a : Fin 4 → Bool → F)
    (o : AlignedPartialOffsets d hd σ g c J a) (i : Fin 4) (hi : i ∈ J) :
    tuplePositionEquiv d hd σ o.1.1 i =
      (lineEvalEquiv (d i) g (hg i)).symm (a i (σ i), c) := by
  apply (lineEvalEquiv (d i) g (hg i)).injective
  rw [Equiv.apply_symm_apply]
  apply Prod.ext
  · change lineEval (d i) (tuplePositionEquiv d hd σ o.1.1 i) = a i (σ i)
    rw [tuplePosition_lineEval_left, o.1.2 i hi]
  · exact o.2 i

omit [Fintype F] [DecidableEq F] in

theorem alignedPartial_position_old_right (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (hg : ∀ i, d i ≠ g) (c : F)
    (J : Finset (Fin 4)) (a : Fin 4 → Bool → F)
    (o : AlignedPartialOffsets d hd σ g c J a) (i : Fin 4) (hi : i + 1 ∈ J) :
    tuplePositionEquiv d hd σ o.1.1 i =
      (lineEvalEquiv (d (i+1)) g (hg (i+1))).symm (a (i+1) (!(σ (i+1))), c) := by
  apply (lineEvalEquiv (d (i+1)) g (hg (i+1))).injective
  rw [Equiv.apply_symm_apply]
  apply Prod.ext
  · change lineEval (d (i+1)) (tuplePositionEquiv d hd σ o.1.1 i) = a (i+1) (!(σ (i+1)))
    rw [tuplePosition_lineEval_right, o.1.2 (i+1) hi]
  · exact o.2 i

end
end Balanced.AlignedListProbability

end OAI
