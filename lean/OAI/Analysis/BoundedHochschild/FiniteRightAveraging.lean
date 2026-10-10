import OAI.Analysis.BoundedHochschild.ColumnRowEstimates

namespace OAI

/-!
# Elementary right averages of bounded linear maps

These are the finite averages used in the completely bounded module-map
projection. The norm estimate only uses the precise finite-row inequality.
-/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {M : Type*} [CStarAlgebra M]

/-- A finite-row bound, expressed in the C*-algebra without an auxiliary
operator-space structure. -/
def HasFiniteRowBound (T : M →L[ℂ] M) (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ (n : ℕ) (x : Fin n → M),
    ‖∑ i, T (x i) * star (T (x i))‖ ≤ C ^ 2 * ‖∑ i, x i * star (x i)‖

variable {I : Type*} [Fintype I]

/-- The elementary average `x ↦ ∑ T(x mᵢ) mᵢ*`. -/
def finiteRightAverage (m : I → M) (T : M →L[ℂ] M) : M →L[ℂ] M :=
  ∑ i, ((ContinuousLinearMap.mul ℂ M).flip (star (m i))).comp
    (T.comp ((ContinuousLinearMap.mul ℂ M).flip (m i)))

@[simp] lemma finiteRightAverage_apply (m : I → M) (T : M →L[ℂ] M) (a : M) :
    finiteRightAverage m T a = ∑ i, T (a * m i) * star (m i) := by
  simp only [finiteRightAverage, sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.mul_apply', ContinuousLinearMap.flip_apply]

lemma finiteRightAverage_add (m : I → M) (S T : M →L[ℂ] M) :
    finiteRightAverage m (S + T) = finiteRightAverage m S + finiteRightAverage m T := by
  ext a
  simp only [finiteRightAverage_apply, add_apply, add_mul, Finset.sum_add_distrib]

lemma finiteRightAverage_smul (m : I → M) (z : ℂ) (T : M →L[ℂ] M) :
    finiteRightAverage m (z • T) = z • finiteRightAverage m T := by
  ext a
  simp only [finiteRightAverage_apply, smul_apply, smul_mul_assoc,
    Finset.smul_sum]

lemma finiteRightAverage_leftOutput (m : I → M) (b : M) (T : M →L[ℂ] M) :
    finiteRightAverage m ((ContinuousLinearMap.mul ℂ M b).comp T) =
      (ContinuousLinearMap.mul ℂ M b).comp (finiteRightAverage m T) := by
  ext a
  simp only [finiteRightAverage_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.mul_apply', Finset.mul_sum, mul_assoc]

lemma finiteRightAverage_precompose_left (m : I → M) (b : M) (T : M →L[ℂ] M) :
    finiteRightAverage m (T.comp (ContinuousLinearMap.mul ℂ M b)) =
      (finiteRightAverage m T).comp (ContinuousLinearMap.mul ℂ M b) := by
  ext a
  simp only [finiteRightAverage_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.mul_apply', mul_assoc]

lemma finiteRightAverage_mul_left (m : I → M) (hm : ∑ i, m i * star (m i) = 1) (b : M) :
    finiteRightAverage m (ContinuousLinearMap.mul ℂ M b) = ContinuousLinearMap.mul ℂ M b := by
  ext a
  simp only [finiteRightAverage_apply, ContinuousLinearMap.mul_apply']
  calc
    _ = b * a * (∑ i, m i * star (m i)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [mul_assoc]
    _ = b * a := by rw [hm, mul_one]

variable {n : ℕ}

/-- Finite normalized right averages satisfy the row norm bound. -/
theorem finiteRightAverage_norm_of_rowBound
    (c : Fin n → HochschildComparison.PartialIso M)
    (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0)
    (m : Fin n → M) (hm : ∑ i, m i * star (m i) = 1)
    (T : M →L[ℂ] M) {C : ℝ} (hT : HasFiniteRowBound T C) :
    ‖finiteRightAverage m T‖ ≤ C := by
  by_cases hM : Nontrivial M
  · let := hM
    apply ContinuousLinearMap.opNorm_le_bound _ hT.1
    intro a
    have hin : (∑ i, (a * m i) * star (a * m i)) = a * star a := by
      calc
        _ = a * (∑ i, m i * star (m i)) * star a := by
          simp only [Finset.mul_sum, Finset.sum_mul, star_mul, mul_assoc]
        _ = a * star a := by rw [hm, mul_one]
    have hs : ‖finiteRightAverage m T a‖ ^ 2 ≤ C ^ 2 * ‖a‖ ^ 2 := by
      rw [finiteRightAverage_apply]
      calc
        _ ≤ ‖∑ i, T (a * m i) * star (T (a * m i))‖ *
            ‖∑ i, star (star (m i)) * star (m i)‖ :=
          finite_row_column_estimate c hi ho (fun i => T (a * m i)) (fun i => star (m i))
        _ = ‖∑ i, T (a * m i) * star (T (a * m i))‖ := by
          simp only [star_star, hm, norm_one, mul_one]
        _ ≤ C ^ 2 * ‖∑ i, (a * m i) * star (a * m i)‖ := hT.2 n (fun i => a * m i)
        _ = C ^ 2 * ‖a‖ ^ 2 := by simp only [hin, CStarRing.norm_self_mul_star, sq]
    have hnonneg : 0 ≤ C * ‖a‖ := mul_nonneg hT.1 (norm_nonneg a)
    nlinarith [norm_nonneg (finiteRightAverage m T a)]
  · let : Subsingleton M := not_nontrivial_iff_subsingleton.mp hM
    have hz : finiteRightAverage m T = 0 := Subsingleton.elim _ _
    rw [hz, norm_zero]
    exact hT.1

end BoundedHochschild.KadisonRingrose

end

end OAI
