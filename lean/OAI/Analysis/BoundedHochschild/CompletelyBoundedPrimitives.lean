import OAI.Analysis.BoundedHochschild.CompletelyBoundedLastSlices

namespace OAI

/-! The module projection contracts the Hochschild complex on cochains with
uniformly completely bounded last slices. The argument is the one-sided
module homotopy underlying completely bounded cohomology vanishing. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

lemma cb_cocycle_last_relation {n : ℕ} (f : Cochain M (n + 1)) {C : ℝ}
    (hs : LastSliceEstimate f C)
    (hf : ∀ x, differentialValue f x = 0) (v : Fin (n + 1) → M) :
    cbLeftSandwich (v 0) 1 (cbCurryRight f hs (fun i => v i.succ)) +
      (∑ j : Fin n, ((-1 : ℂ) ^ (j.val + 1)) • cbCurryRight f hs (mergeInputs v j)) +
      ((-1 : ℂ) ^ (n + 1)) •
        cbLeftSandwich 1 (v (Fin.last n)) (cbCurryRight f hs (fun i => v i.castSucc)) +
      ((-1 : ℂ) ^ (n + 2)) • cbLeftMul (f v) = 0 := by
  apply Subtype.ext
  ext u
  have h := hf (Fin.snoc v u)
  rw [differentialValue_snoc] at h
  simpa [cbLeftSandwich, leftSandwichMap, cbCurryRight_val] using h

lemma averagedLastCochain_differential [Nontrivial M]
    (P : RightModuleAveragingProjection (M := M)) {n : ℕ}
    (f : Cochain M (n + 1)) {C : ℝ} (hs : LastSliceEstimate f C)
    (hf : ∀ x, differentialValue f x = 0) (v : Fin (n + 1) → M) :
    differentialValue (averagedLastCochain P f hs) v =
      ((-1 : ℂ) ^ (n + 1)) • f v := by
  have h := congrArg (fun T : CompletelyBoundedMap M => P.map T 1)
    (cb_cocycle_last_relation f hs hf v)
  simp only [map_add, map_sum, map_smul, add_apply,
    sum_apply, smul_apply,
    P.covariance, leftSandwichMap_apply, one_mul, mul_one,
    moduleProjection_leftMul, cbLeftMul_apply, map_zero, zero_apply] at h
  have hm := P.module (cbCurryRight f hs (fun i => v i.castSucc)) 1 (v (Fin.last n))
  rw [one_mul] at hm
  rw [hm] at h
  have hp : (-1 : ℂ) ^ (n + 2) = -((-1 : ℂ) ^ (n + 1)) := by
    rw [show n + 2 = n + 1 + 1 by omega, pow_succ]
    ring
  rw [hp, neg_smul] at h
  apply eq_of_sub_eq_zero
  simpa only [differentialValue, averagedLastCochain_apply, sub_eq_add_neg] using h

theorem primitive_of_lastSliceEstimate [Nontrivial M]
    (P : RightModuleAveragingProjection (M := M)) {n : ℕ}
    (f : Cochain M (n + 1)) {C : ℝ} (hs : LastSliceEstimate f C)
    (hf : ∀ x, differentialValue f x = 0) :
    ∃ g : Cochain M n, ‖g‖ ≤ C ∧ ∀ x, differentialValue g x = f x := by
  let g := ((-1 : ℂ) ^ (n + 1)) • averagedLastCochain P f hs
  refine ⟨g, ?_, fun x => ?_⟩
  · simpa only [g, norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul] using
      averagedLastCochain_norm P f hs
  · change differentialValue (((-1 : ℂ) ^ (n + 1)) • averagedLastCochain P f hs) x = f x
    rw [differentialValue_smul, averagedLastCochain_differential P f hs hf,
      smul_smul, ← mul_pow, neg_mul_neg, one_mul, one_pow, one_smul]

universe u
variable {N X : Type u} [CStarAlgebra N] [PartialOrder N] [StarOrderedRing N]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem properlyInfinite_primitive_of_lastSliceEstimate [Nontrivial N]
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] N) (hno : NoFiniteCentralSummand N) {n : ℕ}
    (f : Cochain N (n + 1)) {C : ℝ} (hs : LastSliceEstimate f C)
    (hf : ∀ x, differentialValue f x = 0) :
    ∃ g : Cochain N n, ‖g‖ ≤ C ∧ ∀ x, differentialValue g x = f x := by
  obtain ⟨P⟩ := exists_rightModuleAveragingProjection e hno
  exact primitive_of_lastSliceEstimate P f hs hf

end BoundedHochschild.KadisonRingrose

end

end OAI
