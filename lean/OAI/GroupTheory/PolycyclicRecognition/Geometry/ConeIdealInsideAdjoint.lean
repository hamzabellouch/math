import OAI.GroupTheory.PolycyclicRecognition.Analysis.ConeIdealBoxCalculus
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanBoxMaps

namespace OAI

/-! # Uniform ideal-box bounds for an inside adjoint

An inside letter has width zero. Adjoining it to a mixed word leaves the
width unchanged, so maximizing-basis exchange bounds its adjoint uniformly
in every rescaled ideal box.
-/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieModule LieAlgebra

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  (C : Set (H →ₗ[ℝ] ℝ))

def coneIdealLetterAdjoint (i : Fin M.letterCount) :
    Module.End ℝ (M.coneWordIdeal C) :=
  toEnd ℝ (cartanRootIdeal H) (M.coneWordIdeal C) (M.letter i)

theorem coneIdealLetterAdjoint_nilpotent (i : Fin M.letterCount) :
    (M.coneIdealLetterAdjoint C i) ^ M.bound = 0 := by
  let D := M.coneIdealLetterAdjoint C i
  have hiter (j : ℕ) (v : M.coneWordIdeal C) :
      ((D ^ j) v : cartanRootIdeal H) =
        (toEnd ℝ (cartanRootIdeal H) (cartanRootIdeal H) (M.letter i))^[j] v := by
    induction j with
    | zero => rfl
    | succ j hj =>
      rw [pow_succ', Module.End.mul_apply, Function.iterate_succ_apply']
      change ⁅M.letter i, ((D ^ j) v : cartanRootIdeal H)⁆ = _
      rw [hj]
      rfl
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  change ((D ^ M.bound) v : cartanRootIdeal H) = 0
  rw [hiter]
  have hz := iterate_toEnd_mem_lowerCentralSeries ℝ (cartanRootIdeal H)
    (cartanRootIdeal H) (M.letter i) (v : cartanRootIdeal H) M.bound
  rw [M.bound_zero] at hz
  exact hz

/-- A uniform bound for the actual restricted adjoint in all maximizing
ideal-box coordinates. The letter need only have zero prescribed width. -/
theorem exists_uniform_coneIdealLetterAdjoint_bound
    (b₀ : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (s : Fin M.letterCount → ℝ) (β : M.ConeIdealBases C),
      M.IsMaximizingConeIdealBasis C b₀ s β →
      ∀ (i : Fin M.letterCount), s i = 0 → ∀ r : ℝ, 0 ≤ r →
      ∀ v : M.coneWordIdeal C,
      ‖(M.coneIdealBoxBasis C s β r).equivFun (M.coneIdealLetterAdjoint C i v)‖ ≤
        A * ‖(M.coneIdealBoxBasis C s β r).equivFun v‖ := by
  obtain ⟨K, hK, hword⟩ := exists_uniform_rescaled_word_bound
    (M.coneMixedVector C) (M.coneIdealWordList C) b₀
  refine ⟨(finrank ℝ (M.coneWordIdeal C) : ℝ) * K,
    mul_nonneg (Nat.cast_nonneg _) hK, ?_⟩
  intro s β hβ i hi r hr v
  let b := WordBasisSelections.basis (M.coneMixedVector C) (M.coneIdealWordList C) β
  let br := M.coneIdealBoxBasis C s β r
  let D := M.coneIdealLetterAdjoint C i
  have hbr (j) : br j = Real.exp (r * M.coneIdealWordCost C s (β.val j)) • b j := by
    simp only [br, coneIdealBoxBasis, exponentialRescaleBasis, Basis.unitsSMul_apply,
      Units.smul_def, Units.val_mk0, b]
  have hb (j : Fin (finrank ℝ (M.coneWordIdeal C))) :
      ‖br.equivFun (D (br j))‖ ≤ K := by
    by_cases hz : D (b j) = 0
    · have he : D (br j) = 0 := by
        rw [hbr, map_smul, hz, smul_zero]
      rw [he, map_zero, norm_zero]
      exact hK
    · let u := M.coneOriginalWord C (β.val j)
      have hbu : evalBracketWord M.letter u = (b j : cartanRootIdeal H) := by
        rw [M.coneOriginalWord_eval]
        exact congrArg Subtype.val
          (WordBasisSelections.eval_words (M.coneMixedVector C) (M.coneIdealWordList C) β j)
      have hnonzero : evalBracketWord M.letter (FreeMagma.of i * u) ≠ 0 := by
        rw [evalBracketWord_mul, evalBracketWord_of, hbu]
        exact fun h => hz (Subtype.ext h)
      let w : M.coneMixedWords C :=
        ⟨⟨FreeMagma.of i * u, M.mem_wordList_of_eval_ne_zero _ hnonzero⟩,
          Or.inr (M.coneOriginalWord_mixed C (β.val j))⟩
      have hw : M.coneMixedVector C w = D (b j) := by
        apply Subtype.ext
        change evalBracketWord M.letter (FreeMagma.of i * u) = _
        rw [evalBracketWord_mul, evalBracketWord_of, hbu]
        rfl
      have hmem : FreeMagma.of w ∈ M.coneIdealWordList C := by
        apply (mem_boundedBracketWords _ _).mpr
        change 0 < M.coneIdealWordBound C
        by_contra hn
        have hh := evalBracketWord_eq_zero_of_depth (M.coneMixedVector C)
          (M.coneIdealWordBound_zero C) (FreeMagma.of w)
          (by simpa only [bracketWordDepth] using Nat.le_of_not_gt hn)
        exact hz (hw.symm.trans hh)
      have hcost : M.coneIdealWordCost C s (FreeMagma.of w) =
          M.coneIdealWordCost C s (β.val j) := by
        change bracketWordExponent
          (fun z : M.coneMixedWords C => bracketWordExponent s z.val.val)
          (FreeMagma.of w) = _
        rw [bracketWordExponent_of]
        change bracketWordExponent s (FreeMagma.of i * u) = _
        rw [bracketWordExponent_mul, bracketWordExponent_of, hi, zero_add,
          M.coneIdealWordCost_eq_original]
      have hh := hword (fun z => M.coneIdealWordCost C s z) β hβ r hr
        ⟨FreeMagma.of w, hmem⟩
      change ‖br.equivFun (Real.exp (r * M.coneIdealWordCost C s (FreeMagma.of w)) •
        M.coneMixedVector C w)‖ ≤ K at hh
      rw [hcost, hw] at hh
      rw [hbr, map_smul]
      exact hh
  simpa only [Fintype.card_fin] using norm_basis_linearMap_le br D hb v

end PolycyclicRecognition.CartanWordModel

end

end OAI
