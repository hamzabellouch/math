import OAI.Probability.EntangledGames.SpectralEntropy

namespace OAI

universe u_n u_α u_m u_p u_J u_R

open scoped BigOperators ComplexOrder
open scoped MatrixOrder
open Matrix
open MeasureTheory Filter Set
open scoped Topology
open scoped Matrix.Norms.Elementwise

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Elementwise Topology
open Matrix MeasureTheory Filter Set
namespace ThresholdParallelRepetition.Resolvent
attribute [local instance] matrixContinuousENorm matrixPreorder matrixClosedIci rectContinuousENorm
variable {n : Type u_n} [Fintype n] [DecidableEq n]

lemma integral_matrix_apply {α : Type u_α} [MeasurableSpace α] {μ : Measure α}
    {m : Type u_m} {p : Type u_p} [Fintype m] [Fintype p] {f : α → Matrix m p ℂ}
    (hf : Integrable f μ) (i : m) (j : p) :
    (∫ s, f s ∂μ) i j = ∫ s, f s i j ∂μ := by
  erw [eval_integral (fun i => hf.eval i), eval_integral (fun j => (hf.eval i).eval j)]

variable {J : Type u_J} [Fintype J] [DecidableEq J]

def commonKernel (A : J → Matrix n n ℂ) (s : ℝ) : Matrix n (J × n) ℂ :=
  fun r v => purificationKernel (A v.1) s r v.2

def commonGram (A : J → Matrix n n ℂ) : Matrix (J × n) (J × n) ℂ :=
  ∫ s : ℝ in Ioi 0, (commonKernel A s)ᴴ * commonKernel A s

omit [DecidableEq J] in
lemma commonGram_integrable (A : J → Matrix n n ℂ) (hA : ∀ j, (A j).PosSemidef) :
    IntegrableOn (fun s : ℝ => (commonKernel A s)ᴴ * commonKernel A s) (Ioi 0) := by
  apply integrable_gram <;> intro i j <;> exact kernel_entry_memLp (hA j.1) i j.2

lemma commonGram_posSemidef (A : J → Matrix n n ℂ) : (commonGram A).PosSemidef := by
  apply integral_matrix_nonneg
  exact Filter.Eventually.of_forall fun s => posSemidef_conjTranspose_mul_self (commonKernel A s)

omit [DecidableEq J] in
lemma commonGram_block (A : J → Matrix n n ℂ) (hA : ∀ j, (A j).PosSemidef) (j k : J) :
    (commonGram A).submatrix (fun i => (j, i)) (fun i => (k, i)) =
      ∫ s : ℝ in Ioi 0, (purificationKernel (A j) s)ᴴ * purificationKernel (A k) s := by
  ext i l
  change (∫ s : ℝ in Ioi 0, (commonKernel A s)ᴴ * commonKernel A s) (j, i) (k, l) = _
  rw [integral_matrix_apply (commonGram_integrable A hA),
    integral_matrix_apply (kernel_cross_integrable (hA j) (hA k))]
  rfl

def finitePurification (A : J → Matrix n n ℂ) (j : J) : Matrix (J × n) n ℂ :=
  (CFC.sqrt (commonGram A)).submatrix id (fun i => (j, i))

lemma finitePurification_product (A : J → Matrix n n ℂ)
    (hA : ∀ j, (A j).PosSemidef) (j k : J) :
    (finitePurification A j)ᴴ * finitePurification A k =
      ∫ s : ℝ in Ioi 0, (purificationKernel (A j) s)ᴴ * purificationKernel (A k) s := by
  have hh := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (commonGram A))).isHermitian.eq
  unfold finitePurification
  rw [Matrix.conjTranspose_submatrix]
  change (CFC.sqrt (commonGram A))ᴴ.submatrix (fun i => (j, i)) (Equiv.refl (J × n)) *
      (CFC.sqrt (commonGram A)).submatrix (Equiv.refl (J × n)) (fun i => (k, i)) = _
  rw [Matrix.submatrix_mul_equiv, hh,
    CFC.sqrt_mul_sqrt_self (commonGram A) (commonGram_posSemidef A).nonneg]
  exact commonGram_block A hA j k

lemma finitePurification_self (A : J → Matrix n n ℂ)
    (hA : ∀ j, (A j).PosSemidef) (j : J) :
    (finitePurification A j)ᴴ * finitePurification A j = A j := by
  rw [finitePurification_product A hA, kernel_square_integral (hA j)]

lemma finitePurification_distance (A : J → Matrix n n ℂ)
    (hA : ∀ j, (A j).PosSemidef) (j k : J) :
    (finitePurification A j - finitePurification A k)ᴴ *
      (finitePurification A j - finitePurification A k) =
      ∫ s : ℝ in Ioi 0, (purificationKernel (A j) s - purificationKernel (A k) s)ᴴ *
        (purificationKernel (A j) s - purificationKernel (A k) s) := by
  conv_lhs => rw [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
  have hd (s : ℝ) :
      (purificationKernel (A j) s - purificationKernel (A k) s)ᴴ *
        (purificationKernel (A j) s - purificationKernel (A k) s) =
      ((purificationKernel (A j) s)ᴴ * purificationKernel (A j) s -
        (purificationKernel (A j) s)ᴴ * purificationKernel (A k) s) -
      ((purificationKernel (A k) s)ᴴ * purificationKernel (A j) s -
        (purificationKernel (A k) s)ᴴ * purificationKernel (A k) s) := by
    rw [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
  simp_rw [hd]
  erw [integral_sub ((kernel_cross_integrable (hA j) (hA j)).sub
      (kernel_cross_integrable (hA j) (hA k)))
      ((kernel_cross_integrable (hA k) (hA j)).sub (kernel_cross_integrable (hA k) (hA k))),
    integral_sub (kernel_cross_integrable (hA j) (hA j)) (kernel_cross_integrable (hA j) (hA k)),
    integral_sub (kernel_cross_integrable (hA k) (hA j)) (kernel_cross_integrable (hA k) (hA k))]
  simp only [finitePurification_product A hA]

lemma finitePurification_jensen {R : Type u_R} [Fintype R]
    (A : J → Matrix n n ℂ) (hA : ∀ j, (A j).PosSemidef) (hA1 : ∀ j, A j ≤ 1)
    (e : R → J) (w : R → ℝ) (k : J)
    (hw0 : ∀ r, 0 ≤ w r) (hw : ∑ r, w r = 1)
    (hmean : ∑ r, w r • A (e r) = A k) :
    (∑ r, w r • ((finitePurification A (e r) - finitePurification A k)ᴴ *
      (finitePurification A (e r) - finitePurification A k))) ≤
      (∑ r, w r • effectEntropy (A (e r))) - effectEntropy (A k) := by
  simp_rw [finitePurification_distance A hA]
  exact weighted_distance_jensen (A ∘ e) w (A k) (fun r => hA (e r))
    (fun r => hA1 (e r)) (hA k) (hA1 k) hw0 hw hmean

theorem finite_common_purification (A : J → Matrix n n ℂ)
    (hA : ∀ j, (A j).PosSemidef) :
    ∃ F : J → Matrix (J × n) n ℂ,
      (∀ j, (F j)ᴴ * F j = A j) ∧
      ∀ j k, (F j)ᴴ * F k =
        ∫ s : ℝ in Ioi 0, (purificationKernel (A j) s)ᴴ * purificationKernel (A k) s :=
  ⟨finitePurification A, finitePurification_self A hA, finitePurification_product A hA⟩

end ThresholdParallelRepetition.Resolvent

end

end OAI
