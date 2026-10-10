import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanConeGroup
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanGroupBoxes
import OAI.GroupTheory.PolycyclicRecognition.Algebra.ConeIdealBasisExchange

namespace OAI

/-! # Actual quotient images of zero-width Cartan boxes

Mixed words vanish in the cone quotient. Every remaining word has exponent
zero, so projection of a full box has a radius independent of the scale.
-/

noncomputable section
namespace PolycyclicRecognition

open Module LieModule Set

section Linear

variable {I L V : Type*} [LieRing L] [LieAlgebra ℝ L]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A linear projection annihilating all words with nonzero cost has a
uniform norm bound on every rescaled word basis. -/
theorem exists_zero_width_word_projection_bound
    (X : I → L) (S : Finset (FreeMagma I)) (q : L →ₗ[ℝ] V) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (β : WordBasisSelections X S) (cost : S → ℝ),
      (∀ w : S, q (evalBracketWord X w) ≠ 0 → cost w = 0) →
      ∀ (r : ℝ) (v : L), ‖q v‖ ≤ C *
        ‖(exponentialRescaleBasis (WordBasisSelections.basis X S β)
          (fun j => cost (β.val j)) r).equivFun v‖ := by
  let A := ∑ w : S, ‖q (evalBracketWord X w)‖
  have hA : 0 ≤ A := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hAw (w : S) : ‖q (evalBracketWord X w)‖ ≤ A :=
    Finset.single_le_sum (f := fun w : S => ‖q (evalBracketWord X w)‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ w)
  refine ⟨(finrank ℝ L : ℝ) * A, mul_nonneg (Nat.cast_nonneg _) hA, ?_⟩
  intro β cost hcost r v
  let b := exponentialRescaleBasis (WordBasisSelections.basis X S β)
    (fun j => cost (β.val j)) r
  have hb (j : Fin (finrank ℝ L)) : ‖q (b j)‖ ≤ A := by
    have he : b j = Real.exp (r * cost (β.val j)) • evalBracketWord X (β.val j) := by
      have hj := WordBasisSelections.eval_words X S β j
      change evalBracketWord X (β.val j) = _ at hj
      rw [hj]
      simp only [b, exponentialRescaleBasis, Basis.unitsSMul_apply,
        Units.smul_def, Units.val_mk0]
    rw [he, map_smul]
    by_cases hz : q (evalBracketWord X (β.val j)) = 0
    · simpa only [hz, smul_zero, norm_zero] using hA
    · rw [hcost (β.val j) hz, mul_zero, Real.exp_zero, one_smul]
      exact hAw (β.val j)
  change ‖q v‖ ≤ _ * ‖b.equivFun v‖
  conv_lhs => rw [← b.sum_repr v]
  rw [map_sum]
  calc
    _ ≤ ∑ j, ‖q (b.repr v j • b j)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin (finrank ℝ L), ‖b.equivFun v‖ * A := by
      apply Finset.sum_le_sum
      intro j _
      rw [map_smul, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (norm_le_pi_norm (b.equivFun v) j) (hb j) (norm_nonneg _) (norm_nonneg _)
    _ = (finrank ℝ L : ℝ) * A * ‖b.equivFun v‖ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

end Linear

namespace CartanWordModel

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  (C : Set (H →ₗ[ℝ] ℝ))

/-- A word survives the cone projection only when all its letters are
inside the cone, hence has cost zero under the stated letter costs. -/
theorem coneProjection_word_cost_eq_zero
    (s : Fin M.letterCount → ℝ)
    (hzero : ∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∈ C → s i = 0)
    (w : FreeMagma (Fin M.letterCount))
    (hw : M.coneProjection C (evalBracketWord M.letter w) ≠ 0) :
    bracketWordExponent s w = 0 := by
  have hpure : ¬IsMixedWord (fun i => (M.weight i : H →ₗ[ℝ] ℝ) ∉ C) w := by
    intro hmix
    apply hw
    exact (Submodule.Quotient.mk_eq_zero (M.coneWordIdeal C).toSubmodule).mpr
      (eval_mixed_mem_span M.letter _ hmix)
  exact bracketWordExponent_eq_zero_of_pure s _
    (fun i hi => hzero i (not_not.mp hi)) w hpure

/-- The true group quotient sends every zero-width full box into a fixed
multiple of the quotient logarithmic box. Neither the radius nor the
constant contains an exponential scale factor. -/
theorem exists_cone_quotient_box_bound {N Q : Type*} [Group N] [Group Q]
    (ExpN : cartanRootIdeal H → N)
    (ExpQ : ((cartanRootIdeal H) ⧸ M.coneWordIdeal C) → Q)
    (π : N →* Q) (hπ : ∀ v, π (ExpN v) = ExpQ (M.coneProjection C v))
    {n : ℕ} (bQ : Basis (Fin n) ℝ ((cartanRootIdeal H) ⧸ M.coneWordIdeal C)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (β : M.Bases) (s : Fin M.letterCount → ℝ),
      (∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∈ C → s i = 0) →
      ∀ r R : ℝ, π '' exponentialCoordinateBox ExpN
        (exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
          (fun j => bracketWordExponent s (β.val j)) r) R ⊆
        exponentialCoordinateBox ExpQ bQ (A * R) := by
  let q := bQ.equivFun.toLinearMap.comp (M.coneProjection C).toLinearMap
  obtain ⟨A, hA, hbound⟩ := exists_zero_width_word_projection_bound M.letter M.wordList q
  refine ⟨A, hA, ?_⟩
  intro β s hzero r R x hx
  obtain ⟨y, ⟨v, rfl, hv⟩, rfl⟩ := hx
  refine ⟨M.coneProjection C v, (hπ v).symm, ?_⟩
  apply (hbound β (fun w => bracketWordExponent s w) ?_ r v).trans
    (mul_le_mul_of_nonneg_left hv hA)
  intro w hw
  apply M.coneProjection_word_cost_eq_zero C s hzero w
  intro hz
  apply hw
  change bQ.equivFun (M.coneProjection C (evalBracketWord M.letter w)) = 0
  rw [hz, map_zero]

end CartanWordModel
end PolycyclicRecognition

end

end OAI
