import OAI.Analysis.Pureness.Completion.NonUnitalRoots

namespace OAI
noncomputable section
namespace CuntzPureness
open Filter Topology
open scoped ComplexOrder ENNReal NNReal
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def completedRootRank (τ : TracialState A) (a : CornerCompletion A) : ℝ≥0∞ :=
  ⨆ n : ℕ, completedDiagonalWeight τ (nonUnitalRoot a n)

lemma completedRootRank_normalized_tendsto (τ : TracialState A) (a : CornerCompletion A) (ha : 0 ≤ a) :
    Tendsto (fun n : ℕ => completedDiagonalWeight τ (nonUnitalRoot a n))
      atTop (𝓝 (completedRootRank τ a)) :=
  tendsto_atTop_iSup (fun _ _ hle => completedDiagonalWeight_mono τ (nonUnitalRoot_monotone a ha hle))

@[simp] lemma completedRootRank_zero (τ : TracialState A) : completedRootRank τ 0 = 0 := by
  simp [completedRootRank, nonUnitalRoot, nonUnitalNormalize]

lemma completedRootRank_smul (τ : TracialState A) (a : CornerCompletion A) (s : ℝ) (hs : 0 < s) :
    completedRootRank τ (s • a) = completedRootRank τ a := by
  simp only [completedRootRank, nonUnitalRoot, nonUnitalNormalize_smul a s hs]

theorem completed_root_trace_tendsto_rank (τ : TracialState A) (a : CornerCompletion A) (ha : 0 ≤ a) :
    Tendsto (fun n : ℕ => completedDiagonalWeight τ (CFC.nnrpow a (((n : ℝ≥0) + 1)⁻¹)))
      atTop (𝓝 (completedRootRank τ a)) := by
  by_cases ha0 : a = 0
  · simp only [ha0, CFC.nnrpow_eq_pow, CFC.zero_nnrpow, completedDiagonalWeight_zero, completedRootRank_zero]
    exact tendsto_const_nhds
  have hexp : Tendsto (fun n : ℕ => ((((n : ℝ≥0) + 1)⁻¹ : ℝ≥0) : ℝ)) atTop (𝓝 0) := by
    convert (NNReal.continuous_coe.tendsto 0).comp rootExponent_tendsto using 1
    · funext n; rfl
    · simp only [NNReal.coe_zero]
  have hfactor : Tendsto (fun n : ℕ => ‖a‖ ^ ((((n : ℝ≥0) + 1)⁻¹ : ℝ≥0) : ℝ)) atTop (𝓝 1) := by
    simpa only [Real.rpow_zero] using
      ((tendsto_const_nhds (x := ‖a‖)).rpow hexp (Or.inl (norm_ne_zero_iff.mpr ha0)))
  have hfactor' : Tendsto (fun n : ℕ => ENNReal.ofReal (‖a‖ ^ ((((n : ℝ≥0) + 1)⁻¹ : ℝ≥0) : ℝ)))
      atTop (𝓝 1) := by
    simpa only [Function.comp_def, ENNReal.ofReal_one] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hfactor
  have hroot (n : ℕ) : CFC.nnrpow a (((n : ℝ≥0) + 1)⁻¹) =
      ‖a‖ ^ ((((n : ℝ≥0) + 1)⁻¹ : ℝ≥0) : ℝ) • nonUnitalRoot a n := by
    have hs := nonUnital_nnrpow_smul (nonUnitalNormalize a) (nonUnitalNormalize_nonneg a ha)
      ‖a‖ (norm_nonneg a) (((n : ℝ≥0) + 1)⁻¹) (by positivity)
    have he : ‖a‖ • nonUnitalNormalize a = a := by
      rw [nonUnitalNormalize, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr ha0), one_smul]
    rwa [he] at hs
  have ht := ENNReal.Tendsto.mul hfactor' (by simp)
    (completedRootRank_normalized_tendsto τ a ha) (by simp)
  simpa only [hroot, completedDiagonalWeight_smul τ _ (Real.rpow_nonneg (norm_nonneg a) _), one_mul] using ht

theorem completedRootRank_include (τ : TracialState A) (k : ℕ) [NeZero k]
    (a : MatrixStage A k) (ha : 0 ≤ a) :
    completedRootRank τ (completedMatrixInclude A k a) = matrixRank τ a := by
  apply tendsto_nhds_unique (completed_root_trace_tendsto_rank τ (completedMatrixInclude A k a)
    (completedMatrixInclude_nonneg A k a ha))
  convert matrixPower_trace_tendsto_rank τ a ha using 1
  funext n
  rw [nonUnital_nnrpow_map (completedMatrixInclude A k) (completedMatrixInclude_isometry A k).continuous
      a ha _ (by positivity)]
  exact completedDiagonalWeight_include τ k (positivePower a (((n : ℝ≥0) + 1)⁻¹))
    (by exact CFC.nnrpow_nonneg)
end CuntzPureness

end

end OAI
