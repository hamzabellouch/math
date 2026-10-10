import OAI.Analysis.TriangularHilbert.HeatCost

namespace OAI

universe uι

section

namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma norm_sqrt_gram (R : Matrix ι ι ℂ) : ‖CFC.sqrt (Rᴴ * R)‖ = ‖R‖ := by
  rw [CFC.norm_sqrt _ (Matrix.posSemidef_conjTranspose_mul_self R).nonneg]
  rw [show ‖Rᴴ * R‖ = ‖R‖ * ‖R‖ from CStarRing.norm_star_mul_self,
    Real.sqrt_mul_self (norm_nonneg R)]

lemma norm_traceReal_le (X : Matrix ι ι ℂ) :
    ‖traceReal X‖ ≤ ‖traceRealCLM (ι := ι)‖ * ‖X‖ := by
  exact (traceRealCLM (ι := ι)).le_opNorm X

lemma norm_energy_gram_le (R : Matrix ι ι ℂ) :
    ‖energy (Rᴴ * R)‖ ≤ ‖traceRealCLM (ι := ι)‖ * ‖R‖^3 := by
  calc
    _ ≤ ‖traceRealCLM (ι := ι)‖ * ‖Rᴴ * R * CFC.sqrt (Rᴴ * R)‖ :=
      norm_traceReal_le _
    _ ≤ ‖traceRealCLM (ι := ι)‖ * (‖Rᴴ * R‖ * ‖CFC.sqrt (Rᴴ * R)‖) :=
      mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _)
    _ = _ := by
      rw [norm_sqrt_gram,
        show ‖Rᴴ * R‖ = ‖R‖ * ‖R‖ from CStarRing.norm_star_mul_self]
      ring

lemma energy_gram_nonneg (R : Matrix ι ι ℂ) : 0 ≤ energy (Rᴴ * R) := by
  rw [energy_spectral (Matrix.posSemidef_conjTranspose_mul_self R)]
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg ((Matrix.posSemidef_conjTranspose_mul_self R).eigenvalues_nonneg i)
    (Real.sqrt_nonneg _)

lemma norm_energyGradient_inserted_gram_le (R L : Matrix ι ι ℂ) :
    ‖energyGradient (Rᴴ * R) (Rᴴ * L * R)‖ ≤
      (3/2 : ℝ) * ‖traceRealCLM (ι := ι)‖ * ‖L‖ * ‖R‖^3 := by
  rw [energyGradient_apply, norm_mul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 3/2)]
  have hh : ‖traceReal (CFC.sqrt (Rᴴ * R) * (Rᴴ * L * R))‖ ≤
      ‖traceRealCLM (ι := ι)‖ * (‖R‖ * ((‖R‖ * ‖L‖) * ‖R‖)) := by
    calc
      _ ≤ ‖traceRealCLM (ι := ι)‖ * ‖CFC.sqrt (Rᴴ * R) * (Rᴴ * L * R)‖ :=
        norm_traceReal_le _
      _ ≤ ‖traceRealCLM (ι := ι)‖ * (‖CFC.sqrt (Rᴴ * R)‖ * ‖Rᴴ * L * R‖) :=
        mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ ‖traceRealCLM (ι := ι)‖ * (‖R‖ * ((‖R‖ * ‖L‖) * ‖R‖)) := by
        rw [norm_sqrt_gram]
        gcongr
        calc
          _ ≤ ‖Rᴴ * L‖ * ‖R‖ := norm_mul_le _ _
          _ ≤ (‖Rᴴ‖ * ‖L‖) * ‖R‖ := mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
          _ = _ := by rw [show ‖Rᴴ‖ = ‖R‖ from norm_star R]
  calc
    _ ≤ (3/2 : ℝ) * (‖traceRealCLM (ι := ι)‖ * (‖R‖ * ((‖R‖ * ‖L‖) * ‖R‖))) := by gcongr
    _ = _ := by ring

lemma hessianCost_nonneg (P K : Matrix ι ι ℂ) : 0 ≤ hessianCost P K := by
  unfold hessianCost rootCost
  apply mul_nonneg (by norm_num)
  by_cases hb : BddAbove (Set.range (variation (CFC.sqrt P) K))
  · apply le_csSup hb
    exact ⟨0, by simp [variation, penalty]⟩
  · rw [Real.sSup_of_not_bddAbove hb]

lemma norm_hessianCost_inserted_gram_le (R L : Matrix ι ι ℂ) (hL : L.IsHermitian) :
    ‖hessianCost (Rᴴ * R) (Rᴴ * L * R)‖ ≤
      (3/4 : ℝ) * ‖traceRealCLM (ι := ι)‖ * ‖L‖^2 * ‖R‖^3 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (hessianCost_nonneg _ _)]
  calc
    _ ≤ (3/4 : ℝ) * ‖L‖^2 * energy (Rᴴ * R) := hessianCost_inserted_gram_le R L hL
    _ ≤ (3/4 : ℝ) * ‖L‖^2 * (‖traceRealCLM (ι := ι)‖ * ‖R‖^3) := by
      gcongr
      exact (le_abs_self _).trans (norm_energy_gram_le R)
    _ = _ := by ring

def entryNormConstant (ι : Type uι) [Fintype ι] [DecidableEq ι] : ℝ :=
  ∑ i : ι, ∑ j : ι, ‖(Matrix.single i j (1 : ℂ))‖

lemma entryNormConstant_nonneg : 0 ≤ entryNormConstant ι := by
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => norm_nonneg _))

lemma norm_matrix_le_entries (R : Matrix ι ι ℂ) {M : ℝ} (hM : ∀ i j, ‖R i j‖ ≤ M) :
    ‖R‖ ≤ entryNormConstant ι * M := by
  calc
    _ = ‖∑ i, ∑ j, Matrix.single i j (R i j)‖ := congrArg norm (Matrix.matrix_eq_sum_single R)
    _ ≤ ∑ i, ‖∑ j, Matrix.single i j (R i j)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ∑ j, ‖Matrix.single i j (R i j)‖ := Finset.sum_le_sum (fun _ _ => norm_sum_le _ _)
    _ ≤ ∑ i : ι, ∑ j : ι, ‖Matrix.single i j (1 : ℂ)‖ * M := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [show Matrix.single i j (R i j) = (R i j) • Matrix.single i j (1 : ℂ) by
        rw [Matrix.smul_single]; simp, norm_smul, mul_comm]
      exact mul_le_mul_of_nonneg_left (hM i j) (norm_nonneg _)
    _ = _ := by simp [entryNormConstant, Finset.sum_mul]

end
end TriangularHilbert.MatrixEnergy
end

end OAI
