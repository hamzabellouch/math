import OAI.Analysis.Pureness.Operators.CompressionCompatibility

namespace OAI
noncomputable section
namespace CuntzPureness
open Filter Topology
open scoped ComplexOrder ENNReal
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma completedCornerCut_add (k : ℕ) (a b : CornerCompletion A) :
    completedCornerCut A k (a + b) = completedCornerCut A k a + completedCornerCut A k b := by
  simp only [completedCornerCut, mul_add, add_mul]

lemma completedCornerCut_smul (k : ℕ) (z : ℂ) (a : CornerCompletion A) :
    completedCornerCut A k (z • a) = z • completedCornerCut A k a := by
  simp only [completedCornerCut, mul_smul_comm, smul_mul_assoc]

def completedCompressLinear (k : ℕ) : CornerCompletion A →ₗ[ℂ] MatrixStage A k where
  toFun := completedCompress A k
  map_add' a b := by
    apply (completedMatrixInclude_isometry A k).injective
    rw [include_completedCompress, map_add, include_completedCompress, include_completedCompress,
      completedCornerCut_add]
  map_smul' z a := by
    apply (completedMatrixInclude_isometry A k).injective
    simp only [map_smul, include_completedCompress, completedCornerCut_smul]
    rfl

lemma completedCompress_mono (k : ℕ) : Monotone (completedCompress A k) := by
  intro a b hab
  apply sub_nonneg.mp
  change 0 ≤ completedCompressLinear k b - completedCompressLinear k a
  rw [← map_sub]
  exact completedCompress_nonneg k (b - a) (sub_nonneg.mpr hab)

lemma completedCompress_include_of_le {k l : ℕ} (h : k ≤ l) (a : MatrixStage A k) :
    completedCompress A l (completedMatrixInclude A k a) = corner h a := by
  apply (completedMatrixInclude_isometry A l).injective
  rw [include_completedCompress, completedCornerCut_fixes A h, completedMatrixInclude_corner]

def completedTraceValue (τ : TracialState A) (k : ℕ) (a : CornerCompletion A) : ℝ≥0∞ :=
  ENNReal.ofReal (matrixTrace τ (completedCompress A k a)).re

def completedDiagonalWeight (τ : TracialState A) (a : CornerCompletion A) : ℝ≥0∞ :=
  ⨆ k : ℕ, completedTraceValue τ k a

lemma completedTraceValue_continuous (τ : TracialState A) (k : ℕ) :
    Continuous (completedTraceValue τ k) :=
  ENNReal.continuous_ofReal.comp (Complex.continuous_re.comp
    ((map_continuous (matrixTrace τ)).comp (completedCompress_continuous A k)))

lemma completedTraceValue_mono (τ : TracialState A) (k : ℕ) : Monotone (completedTraceValue τ k) := by
  intro a b hab
  apply ENNReal.ofReal_le_ofReal
  exact (Complex.le_def.mp ((matrixTrace τ).monotone (completedCompress_mono k hab))).1

lemma completedTraceValue_monotone (τ : TracialState A) (a : CornerCompletion A) (ha : 0 ≤ a) :
    Monotone (fun k => completedTraceValue τ k a) := by
  intro k l h
  apply ENNReal.ofReal_le_ofReal
  exact (Complex.le_def.mp (completedCompression_trace_monotone τ a ha h)).1

lemma completedDiagonalWeight_tendsto (τ : TracialState A) (a : CornerCompletion A) (ha : 0 ≤ a) :
    Tendsto (fun k : ℕ => completedTraceValue τ k a) atTop (𝓝 (completedDiagonalWeight τ a)) :=
  tendsto_atTop_iSup (completedTraceValue_monotone τ a ha)

lemma completedDiagonalWeight_mono (τ : TracialState A) : Monotone (completedDiagonalWeight τ) := by
  intro a b hab
  exact iSup_mono fun k => completedTraceValue_mono τ k hab

lemma completedTraceValue_add (τ : TracialState A) (k : ℕ) (a b : CornerCompletion A)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    completedTraceValue τ k (a + b) = completedTraceValue τ k a + completedTraceValue τ k b := by
  have hca : 0 ≤ (matrixTrace τ (completedCompress A k a)).re :=
    (Complex.nonneg_iff.mp ((matrixTrace τ).map_nonneg (completedCompress_nonneg k a ha))).1
  have hcb : 0 ≤ (matrixTrace τ (completedCompress A k b)).re :=
    (Complex.nonneg_iff.mp ((matrixTrace τ).map_nonneg (completedCompress_nonneg k b hb))).1
  change ENNReal.ofReal (matrixTrace τ (completedCompressLinear k (a + b))).re = _
  rw [map_add, map_add, Complex.add_re]
  exact ENNReal.ofReal_add hca hcb

theorem completedDiagonalWeight_add (τ : TracialState A) (a b : CornerCompletion A)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    completedDiagonalWeight τ (a + b) = completedDiagonalWeight τ a + completedDiagonalWeight τ b := by
  apply tendsto_nhds_unique (completedDiagonalWeight_tendsto τ (a + b) (add_nonneg ha hb))
  convert (completedDiagonalWeight_tendsto τ a ha).add (completedDiagonalWeight_tendsto τ b hb) using 1
  funext k
  exact completedTraceValue_add τ k a b ha hb

theorem completedDiagonalWeight_include (τ : TracialState A) (l : ℕ) (a : MatrixStage A l) (ha : 0 ≤ a) :
    completedDiagonalWeight τ (completedMatrixInclude A l a) = ENNReal.ofReal (matrixTrace τ a).re := by
  apply le_antisymm
  · apply iSup_le
    intro k
    have hmono := completedTraceValue_monotone τ (completedMatrixInclude A l a)
      (completedMatrixInclude_nonneg A l a ha) (le_max_left k l)
    refine hmono.trans_eq ?_
    unfold completedTraceValue
    dsimp only
    rw [completedCompress_include_of_le (le_max_right k l), matrixTrace_corner]
  · have ht := le_iSup (fun k => completedTraceValue τ k (completedMatrixInclude A l a)) l
    simpa only [completedDiagonalWeight, completedTraceValue, completedCompress_include] using ht

theorem completedDiagonalWeight_le_of_tendsto (τ : TracialState A) {a : ℕ → CornerCompletion A}
    {b : CornerCompletion A} {r : ℝ≥0∞} (ht : Tendsto a atTop (𝓝 b))
    (hr : ∀ n, completedDiagonalWeight τ (a n) ≤ r) : completedDiagonalWeight τ b ≤ r := by
  apply iSup_le
  intro k
  apply le_of_tendsto ((completedTraceValue_continuous τ k).continuousAt.tendsto.comp ht)
  exact Eventually.of_forall fun n => (le_iSup (fun k => completedTraceValue τ k (a n)) k).trans (hr n)
end CuntzPureness

end

end OAI
