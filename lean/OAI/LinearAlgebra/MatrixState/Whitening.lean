import OAI.LinearAlgebra.MatrixState.QuarterRoot
import OAI.RepresentationTheory.RowColumn.Sectors

namespace OAI

section
noncomputable section
open scoped BigOperators Classical MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace RowColumn.MatrixState
variable {C L : Type*} [Fintype C] [DecidableEq C] [Fintype L]

def stateMean (p : L → ℝ) (S : L → Matrix C C ℂ) : Matrix C C ℂ := ∑ i, p i • S i

def whitenState (A S : Matrix C C ℂ) : Matrix C C ℂ := inverseQuarter A * S * inverseQuarter A

omit [Fintype C] [DecidableEq C] in
lemma stateMean_positive (p : L → ℝ) (S : L → Matrix C C ℂ)
    (hp : ∀ i, 0 ≤ p i) (hS : ∀ i, (S i).PosSemidef) : (stateMean p S).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  exact Finset.sum_nonneg fun i _ => ((hS i).smul (hp i)).nonneg

omit [Fintype C] [DecidableEq C] in
lemma smul_le_stateMean (p : L → ℝ) (S : L → Matrix C C ℂ)
    (hp : ∀ i, 0 ≤ p i) (hS : ∀ i, (S i).PosSemidef) (i : L) : p i • S i ≤ stateMean p S := by
  exact Finset.single_le_sum (fun j _ => ((hS j).smul (hp j)).nonneg) (Finset.mem_univ i)

omit [DecidableEq C] in
lemma stateMean_trace_le_one (p : L → ℝ) (S : L → Matrix C C ℂ)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i=1) (hS : ∀ i, (S i).trace.re ≤ 1) :
    (stateMean p S).trace.re ≤ 1 := by
  change (Matrix.trace (∑ i, p i • S i)).re ≤ 1
  rw [Matrix.trace_sum, Complex.re_sum]
  calc
    _ = ∑ i, p i * (S i).trace.re := by simp
    _ ≤ ∑ i, p i := Finset.sum_le_sum fun i _ => by nlinarith [hS i,hp i]
    _ = 1 := hpsum

lemma mean_support (p : L → ℝ) (S : L → Matrix C C ℂ)
    (hp : ∀ i, 0 ≤ p i) (hS : ∀ i, (S i).PosSemidef) (i : L) (hi : 0 < p i) :
    quarterSupport (stateMean p S) * S i = S i := by
  have hh := quarterSupport_of_le (stateMean p S) (p i • S i)
    (stateMean_positive p S hp hS) ((hS i).smul (hp i)) (smul_le_stateMean p S hp hS i)
  rw [mul_smul_comm] at hh
  exact (smul_right_injective _ (ne_of_gt hi)) hh

lemma whitenState_positive (A S : Matrix C C ℂ) (hS : S.PosSemidef) :
    (whitenState A S).PosSemidef := by
  simpa only [whitenState, (inverseQuarter_positive A).isHermitian.eq] using
    hS.conjTranspose_mul_mul_same (inverseQuarter A)

lemma stateMean_whiten (p : L → ℝ) (S : L → Matrix C C ℂ)
    (hp : ∀ i, 0 ≤ p i) (hS : ∀ i, (S i).PosSemidef) :
    stateMean p (fun i => whitenState (stateMean p S) (S i)) = CFC.sqrt (stateMean p S) := by
  change (∑ i, p i • (inverseQuarter (stateMean p S) * S i * inverseQuarter (stateMean p S))) = _
  rw [show (∑ i, p i • (inverseQuarter (stateMean p S) * S i * inverseQuarter (stateMean p S))) =
    inverseQuarter (stateMean p S) * stateMean p S * inverseQuarter (stateMean p S) by
      simp [stateMean, Finset.mul_sum, Finset.sum_mul]]
  rw [quarter_whitening_mean _ (stateMean_positive p S hp hS), quarter_square]

lemma unwhitenState (p : L → ℝ) (S : L → Matrix C C ℂ)
    (hp : ∀ i, 0 ≤ p i) (hS : ∀ i, (S i).PosSemidef) (i : L) (hi : 0 < p i) :
    quarterRoot (stateMean p S) * whitenState (stateMean p S) (S i) * quarterRoot (stateMean p S) = S i :=
  undo_quarter_whitening _ _ (hS i).isHermitian (mean_support p S hp hS i hi)

lemma stateMean_even (odd : C → Prop) (p : L → ℝ) (S : L → Matrix C C ℂ)
    (hS : ∀ i, S i ∈ evenAlgebra odd) : stateMean p S ∈ evenAlgebra odd := by
  apply (evenAlgebra odd).sum_mem
  intro i _ c d h
  change p i • S i c d=0
  rw [hS i c d h, smul_zero]

lemma sqrt_even (odd : C → Prop) (A : Matrix C C ℂ) (hA : A.PosSemidef)
    (he : A ∈ evenAlgebra odd) : CFC.sqrt A ∈ evenAlgebra odd := by
  intro c d h
  exact sqrt_block_supported odd A hA
    (fun c d hh => he c d (fun hcd => hh (propext hcd))) c d
    (fun he => h (Iff.of_eq he))

lemma quarter_even (odd : C → Prop) (A : Matrix C C ℂ) (hA : A.PosSemidef)
    (he : A ∈ evenAlgebra odd) : quarterRoot A ∈ evenAlgebra odd :=
  sqrt_even odd _ (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)) (sqrt_even odd A hA he)

lemma inverseQuarter_even (odd : C → Prop) (A : Matrix C C ℂ) (hA : A.PosSemidef)
    (he : A ∈ evenAlgebra odd) : inverseQuarter A ∈ evenAlgebra odd := by
  let : IsClosed ((evenAlgebra odd) : Set (Matrix C C ℂ)) :=
    (evenAlgebra odd).toSubalgebra.toSubmodule.closed_of_finiteDimensional
  exact cfc_mem (𝕜 := ℝ) (𝕜' := ℂ) (s := evenAlgebra odd) (fun x : ℝ => x⁻¹) (quarter_even odd A hA he)

lemma whitenState_even (odd : C → Prop) (A S : Matrix C C ℂ) (hA : A.PosSemidef)
    (heA : A ∈ evenAlgebra odd) (heS : S ∈ evenAlgebra odd) : whitenState A S ∈ evenAlgebra odd := by
  exact (evenAlgebra odd).mul_mem
    ((evenAlgebra odd).mul_mem (inverseQuarter_even odd A hA heA) heS)
    (inverseQuarter_even odd A hA heA)
end RowColumn.MatrixState

noncomputable section
open scoped BigOperators Classical MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace RowColumn.MatrixState
variable {C L K : Type*} [Fintype C] [DecidableEq C] [Fintype L] [Fintype K]

/-- The independent marginal mean of the local squared Hilbert--Schmidt factors,
with no invertibility assumption on either average state. -/
lemma independent_overlap_mean (p : L → ℝ) (q : K → ℝ)
    (S : L → Matrix C C ℂ) (T : K → Matrix C C ℂ) (U : Matrix C C ℂ) :
    (∑ i, ∑ j, p i * q j * (S i * U * T j * U.conjTranspose).trace.re) =
      (stateMean p S * U * stateMean q T * U.conjTranspose).trace.re := by
  simp only [stateMean, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
    mul_smul_comm, Matrix.trace_sum, Matrix.trace_smul, Complex.re_sum]
  simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, mul_assoc]
  simp only [Complex.re_sum, Finset.mul_sum, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Quarter-root whitening makes the independent mean at most one, while
preserving singular substates exactly on every occupied fibre. -/
theorem weighted_whitened_mean_le_one (p : L → ℝ) (q : K → ℝ)
    (S : L → Matrix C C ℂ) (T : K → Matrix C C ℂ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ j, 0 ≤ q j)
    (hpsum : ∑ i, p i = 1) (hqsum : ∑ j, q j = 1)
    (hS : ∀ i, (S i).PosSemidef) (hT : ∀ j, (T j).PosSemidef)
    (hStr : ∀ i, (S i).trace.re ≤ 1) (hTtr : ∀ j, (T j).trace.re ≤ 1)
    (U : Matrix C C ℂ) (hU : U ∈ unitary (Matrix C C ℂ)) :
    (∑ i, ∑ j, p i * q j *
      (whitenState (stateMean p S) (S i) * U *
        whitenState (stateMean q T) (T j) * U.conjTranspose).trace.re) ≤ 1 := by
  rw [independent_overlap_mean, stateMean_whiten p S hp hS, stateMean_whiten q T hq hT]
  exact trace_sqrt_conjugate_le_one _ _ U (stateMean_positive p S hp hS)
    (stateMean_positive q T hq hT) (stateMean_trace_le_one p S hp hpsum hStr)
    (stateMean_trace_le_one q T hq hqsum hTtr) hU

lemma local_overlap_nonneg (A B U : Matrix C C ℂ) (hA : A.PosSemidef)
    (hB : B.PosSemidef) : 0 ≤ (A * U * B * U.conjTranspose).trace.re := by
  simpa only [mul_assoc] using trace_mul_psd_nonneg A (U * B * U.conjTranspose)
    hA (hB.mul_mul_conjTranspose_same U)

end RowColumn.MatrixState

end
end
end

end OAI
