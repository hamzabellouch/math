import OAI.Probability.MatroidProphet.Main

namespace OAI

/-!
# Every witness residual belongs to one family fixed before the focal masks

This strengthens the existential residual used in the inherited payoff proof to
cover every system of witnesses, as required by `lem:pattern-family` in the pinned
manuscript. The family is defined from the reference incoming path and lower-group
competition, not from the focal density, guard, or test bits.
-/

namespace MatroidProphet

open Set Finset Pivots

variable {α : Type*} [Fintype α] [LinearOrder α]

/-- All witness choices with the stated total budget are captured. No canonical
choice of basis, and no independence of the selected residual, is assumed. -/
theorem nominalResidualSet_mem_labeledFamily
    (M : Matroid α) (hE : M.E = Set.univ) (κ : ℕ) (hκ : 0 < κ)
    (D C T : ℕ → Set α) (h : ℕ) (U : Finset α)
    (hDU : D h ⊆ (U : Set α)) (hnonloop : ∀ e ∈ U, e ∉ M.closure ∅)
    (ε : Fin 2) (W : ParityWindow (activation h) ε → Set α)
    (hW : ∀ b, W b ⊆ nominalLayerSet M hE κ D C h (U : Set α) ε b)
    (hsum : (∑ b, (W b).ncard) ≤ U.card / κ) :
    (Set.toFinite (nominalResidualSet M hE κ D C T h (U : Set α) ε W)).toFinset ∈
      labeledResidualFamily M U κ (guardedPath M hE κ D C h) (activation h) ε
        (fun b => lowerCompetition M hE κ D C T b.val.val h) := by
  classical
  have hd : Pairwise (fun b c => Disjoint (W b) (W c)) := by
    intro b c hbc
    exact (nominalLayerSet_disjoint M hE κ D C h (U : Set α) ε hbc).mono (hW b) (hW c)
  obtain ⟨Z, hZU, hZcard, β, hβ⟩ := collect_disjoint_witnesses W U
    (fun b => (hW b).trans (nominalLayerSet_subset M hE κ D C h _ ε b)) hd
  apply Finset.mem_image.mpr
  refine ⟨integerResidual M (nominalPath M hE κ D C h) (groupLabel U) (activation h) ε
    (fun b => lowerCompetition M hE κ D C T b.val.val h) (fun w : Z => w.val) β, ?_, ?_⟩
  · apply nominal_residual_mem_family M hE κ hκ D C h U Z hDU hZU
      (hZcard.trans hsum) ε (fun b => lowerCompetition M hE κ D C T b.val.val h)
      (fun b => lowerCompetition_subset_guarded M hE κ D C T b.val.val h) β
    · intro w
      have hw : w.val ∈ W (β w) := by
        rw [← hβ (β w)]
        exact ⟨w, rfl, rfl⟩
      exact (hW (β w) hw).2.2.2.1
    · exact fun i => hnonloop _ (groupLabel_mem U i)
  · exact nominalResidualSet_eq_labeled M hE κ D C T h U Z ε W β hβ

end MatroidProphet

namespace MatroidProphet.MainAlgorithm

open Set Finset Pivots

variable {n : ℕ}

/-- Holding the outside coordinates fixed, the same family captures every focal
mask outcome and every small-budget witness system on that outcome. -/
theorem focalResidualFamily_captures_all
    (M : Matroid (Fin n)) (hE : M.E = Set.univ) (κ : ℕ) (hκ : 0 < κ)
    (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ) (ε : Fin 2)
    (A B C : Finset (Fin n))
    (hA : A ⊆ trueGroup M d s i) (hB : B ⊆ trueGroup M d s i)
    (hC : C ⊆ trueGroup M d s i) (hne : A.Nonempty) :
    let U := trueGroup M d s i
    let f := focalMasks d U A B C
    let h := focalIndex M d s i
    ∀ W : ParityWindow (activation h) ε → Set (Fin n),
      (∀ b, W b ⊆ nominalLayerSet M hE κ (groupMask M f s f.D)
        (groupMask M f s f.C) h (U : Set (Fin n)) ε b) →
      (∑ b, (W b).ncard) ≤ U.card / κ →
      (Set.toFinite (nominalResidualSet M hE κ (groupMask M f s f.D)
        (groupMask M f s f.C) (groupMask M f s f.T) h (U : Set (Fin n)) ε W)).toFinset ∈
        focalResidualFamily M hE κ d s i ε := by
  dsimp only
  intro W hW hsum
  let f := focalMasks d (trueGroup M d s i) A B C
  have hDU : groupMask M f s f.D (focalIndex M d s i) ⊆
      (trueGroup M d s i : Set (Fin n)) := by
    rw [show groupMask M f s f.D (focalIndex M d s i) = (A : Set (Fin n)) from
      focal_group_mask M d s i A B C d.D A hA hne hA]
    exact hA
  have hc := nominalResidualSet_mem_labeledFamily M hE κ hκ
    (groupMask M f s f.D) (groupMask M f s f.C) (groupMask M f s f.T)
    (focalIndex M d s i) (trueGroup M d s i) hDU (trueGroup_nonloop M d s i) ε W hW hsum
  have hF := funext (focal_incoming_path M hE κ d s i A B C hA hB hC hne)
  have hK := funext (fun b : ParityWindow (activation (focalIndex M d s i)) ε =>
    focal_lowerCompetition M hE κ d s i A B C hA hB hC hne b.val.val)
  rw [hF, hK] at hc
  exact hc

/-- The complete uniform-family conclusion of `lem:pattern-family`.
The existential family precedes all three focal masks, including the test mask.
The witness hypotheses are weaker than the manuscript's rank-witness conditions:
only layer membership and the total cardinality budget are needed for capture. -/
theorem uniform_residual_family
    (M : Matroid (Fin n)) (hE : M.E = Set.univ) (κ : ℕ) (hκ : 2 ≤ κ)
    (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ)
    (hsize : κ ≤ (trueGroup M d s i).card) (ε : Fin 2) :
    ∃ family : Finset (Finset (Fin n)),
      (∀ R ∈ family, R ⊆ trueGroup M d s i) ∧
      (family.card : ℝ) ≤ Real.exp
        (1000 * Real.log (κ : ℝ) / (κ : ℝ) * (trueGroup M d s i).card) ∧
      ∀ (A B C : Finset (Fin n)),
        A ⊆ trueGroup M d s i → B ⊆ trueGroup M d s i →
        C ⊆ trueGroup M d s i → A.Nonempty →
        let U := trueGroup M d s i
        let f := focalMasks d U A B C
        let h := focalIndex M d s i
        ∀ W : ParityWindow (activation h) ε → Set (Fin n),
          (∀ b, W b ⊆ nominalLayerSet M hE κ (groupMask M f s f.D)
            (groupMask M f s f.C) h (U : Set (Fin n)) ε b) →
          (∑ b, (W b).ncard) ≤ U.card / κ →
          (Set.toFinite (nominalResidualSet M hE κ (groupMask M f s f.D)
            (groupMask M f s f.C) (groupMask M f s f.T) h (U : Set (Fin n)) ε W)).toFinset ∈
              family := by
  have hU : (trueGroup M d s i).Nonempty := Finset.card_pos.mp (by omega)
  refine ⟨focalResidualFamily M hE κ d s i ε, ?_, ?_, ?_⟩
  · exact labeledResidualFamily_subsets M _ _ _ _ ε _
  · exact labeledResidualFamily_card M hE _ hU κ hκ _ _ ε _
  · intro A B C hA hB hC hne
    exact focalResidualFamily_captures_all M hE κ (by omega) d s i ε A B C hA hB hC hne

end MatroidProphet.MainAlgorithm

namespace MatroidProphet.MainAlgorithm

open Finset

variable {n : ℕ}

/-- Replacing focal coordinates does not change the reference masks. This makes
mask-independence explicit rather than relying only on an existential family. -/
theorem focalReference_focalMasks_invariant
    (M : Matroid (Fin n)) (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ)
    (A B C : Finset (Fin n))
    (hA : A ⊆ trueGroup M d s i) (hB : B ⊆ trueGroup M d s i)
    (hC : C ⊆ trueGroup M d s i) :
    focalReference M (focalMasks d (trueGroup M d s i) A B C) s i =
      focalReference M d s i := by
  classical
  have hdiff (X Y U : Finset (Fin n)) (hY : Y ⊆ U) :
      ((X \ U) ∪ Y) \ U = X \ U := by
    ext e
    simp only [Finset.mem_sdiff, Finset.mem_union]
    exact ⟨fun h => ⟨h.1.resolve_right (fun he => h.2 (hY he)) |>.1, h.2⟩,
      fun h => ⟨Or.inl h, h.2⟩⟩
  unfold focalReference
  simp only [trueGroup_focalMasks]
  simp only [focalMasks, hdiff d.D A _ hA, hdiff d.C B _ hB, hdiff d.T C _ hC]

theorem focalIndex_focalMasks_invariant
    (M : Matroid (Fin n)) (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ)
    (A B C : Finset (Fin n))
    (hA : A ⊆ trueGroup M d s i) (hB : B ⊆ trueGroup M d s i)
    (hC : C ⊆ trueGroup M d s i) :
    focalIndex M (focalMasks d (trueGroup M d s i) A B C) s i = focalIndex M d s i := by
  unfold focalIndex
  rw [focalReference_focalMasks_invariant M d s i A B C hA hB hC]

/-- The actual family is unchanged by all focal density, guard, and test bits,
including outcomes in which the focal group is not listed. -/
theorem focalResidualFamily_focalMasks_invariant
    (M : Matroid (Fin n)) (hE : M.E = Set.univ) (κ : ℕ)
    (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ) (ε : Fin 2)
    (A B C : Finset (Fin n))
    (hA : A ⊆ trueGroup M d s i) (hB : B ⊆ trueGroup M d s i)
    (hC : C ⊆ trueGroup M d s i) :
    focalResidualFamily M hE κ (focalMasks d (trueGroup M d s i) A B C) s i ε =
      focalResidualFamily M hE κ d s i ε := by
  let assemble (r : MainMasks n) (U : Finset (Fin n)) (h : ℕ) :=
    labeledResidualFamily M U κ
      (guardedPath M hE κ (groupMask M r s r.D) (groupMask M r s r.C) h)
      (activation h) ε
      (fun b => lowerCompetition M hE κ (groupMask M r s r.D)
        (groupMask M r s r.C) (groupMask M r s r.T) b.val.val h)
  change assemble (focalReference M (focalMasks d (trueGroup M d s i) A B C) s i)
      (trueGroup M (focalMasks d (trueGroup M d s i) A B C) s i)
      (focalIndex M (focalMasks d (trueGroup M d s i) A B C) s i) =
    assemble (focalReference M d s i) (trueGroup M d s i) (focalIndex M d s i)
  rw [trueGroup_focalMasks, focalReference_focalMasks_invariant M d s i A B C hA hB hC,
    focalIndex_focalMasks_invariant M d s i A B C hA hB hC]

end MatroidProphet.MainAlgorithm

end OAI
