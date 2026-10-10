import Mathlib
import OAI.Geometry.Borsuk.MatrixGeometry.PositiveSlice

namespace OAI

namespace BorsukNine
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator
section TraceSphere
variable {ν : Type*} [Fintype ν] [DecidableEq ν]
local notation "M" => Matrix ν ν ℝ

omit [DecidableEq ν] in
lemma matrix_trace_continuous : Continuous (Matrix.trace : M → ℝ) :=
  (Matrix.traceLinearMap ν ℝ ℝ).continuous_of_finiteDimensional

omit [DecidableEq ν] in
lemma matrix_trace_nonneg {A : M} (hA : 0 ≤ A) : 0 ≤ Matrix.trace A :=
  (Matrix.nonneg_iff_posSemidef.mp hA).trace_nonneg

lemma positive_ball_image : {Q : M | 0 ≤ Q ∧ Matrix.trace Q ≤ 1} =
    flatGram '' Metric.closedBall (0 : EuclideanSpace ℝ (ν × ν)) 1 := by
  ext Q
  constructor
  · rintro ⟨hQ,htr⟩
    let x : EuclideanSpace ℝ (ν × ν) := WithLp.toLp 2 (fun p => CFC.sqrt Q p.1 p.2)
    have hxQ : flatGram x = Q := by
      change CFC.sqrt Q * star (CFC.sqrt Q) = Q
      rw [(CFC.sqrt_nonneg Q).isSelfAdjoint.star_eq]
      exact CFC.sqrt_mul_sqrt_self Q
    have hn : ‖x‖ ^ 2 ≤ 1 := by rw [← flatGram_trace,hxQ]; exact htr
    have hn' : ‖x‖ ≤ 1 := by nlinarith [norm_nonneg x]
    exact ⟨x,by simpa [dist_zero_right] using hn',hxQ⟩
  · rintro ⟨x,hx,rfl⟩
    refine ⟨flatGram_nonneg x,?_⟩
    have hn : ‖x‖ ≤ 1 := by simpa [dist_zero_right] using hx
    rw [flatGram_trace]
    nlinarith [norm_nonneg x]

lemma positive_ball_compact : IsCompact {Q : M | 0 ≤ Q ∧ Matrix.trace Q ≤ 1} := by
  rw [positive_ball_image]
  exact (isCompact_closedBall (0 : EuclideanSpace ℝ (ν × ν)) 1).image flatGram_continuous

noncomputable def traceSphere (ν : Type*) [Fintype ν] [DecidableEq ν] : Set (Matrix ν ν ℝ) :=
  {A | IsSelfAdjoint A ∧ Matrix.trace (CFC.abs A) = 1}

lemma traceSphere_closed : IsClosed (traceSphere ν) :=
  (isClosed_eq continuous_star continuous_id).inter
    (isClosed_eq (matrix_trace_continuous.comp CFC.continuous_abs) continuous_const)

lemma traceSphere_compact : IsCompact (traceSphere ν) := by
  have hK : IsCompact ((fun p : M × M => p.1 - p.2) ''
      ({Q : M | 0 ≤ Q ∧ Matrix.trace Q ≤ 1} ×ˢ {Q : M | 0 ≤ Q ∧ Matrix.trace Q ≤ 1})) :=
    (positive_ball_compact.prod positive_ball_compact).image (continuous_fst.sub continuous_snd)
  apply hK.of_isClosed_subset traceSphere_closed
  intro A hA
  have htr : Matrix.trace A⁺ + Matrix.trace A⁻ = 1 := by
    rw [← Matrix.trace_add,CFC.posPart_add_negPart A hA.1]
    exact hA.2
  refine ⟨(A⁺,A⁻),⟨⟨CFC.posPart_nonneg A,?_⟩,⟨CFC.negPart_nonneg A,?_⟩⟩,
    CFC.posPart_sub_negPart A hA.1⟩
  · linarith [matrix_trace_nonneg (CFC.negPart_nonneg A)]
  · linarith [matrix_trace_nonneg (CFC.posPart_nonneg A)]

lemma traceSphere_ne_zero {A : M} (hA : A ∈ traceSphere ν) : A ≠ 0 := by
  intro h
  simpa [h] using hA.2

lemma traceAbs_pos {A : M} (hA : A ≠ 0) : 0 < Matrix.trace (CFC.abs A) := by
  have hp := matrix_trace_nonneg (CFC.abs_nonneg A)
  apply lt_of_le_of_ne hp
  intro hz
  have habs := (Matrix.nonneg_iff_posSemidef.mp (CFC.abs_nonneg A)).trace_eq_zero_iff.mp hz.symm
  have he := CFC.abs_mul_abs A
  rw [habs,zero_mul] at he
  exact hA (Matrix.conjTranspose_mul_self_eq_zero.mp he.symm)

noncomputable def traceRadial (A : M) : M := (Matrix.trace (CFC.abs A))⁻¹ • A

lemma traceRadial_mem {A : M} (hA : IsSelfAdjoint A) (hAz : A ≠ 0) :
    traceRadial A ∈ traceSphere ν := by
  have hp := traceAbs_pos hAz
  refine ⟨(IsSelfAdjoint.all (_ : ℝ)).smul hA,?_⟩
  change Matrix.trace (CFC.abs ((Matrix.trace (CFC.abs A))⁻¹ • A)) = 1
  rw [CFC.abs_smul,Matrix.trace_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hp)]
  exact inv_mul_cancel₀ (ne_of_gt hp)

lemma traceRadial_continuousOn : ContinuousOn (traceRadial (ν := ν)) {A | A ≠ 0} :=
  ((matrix_trace_continuous.comp CFC.continuous_abs).continuousOn.inv₀
    (fun _A hA => ne_of_gt (traceAbs_pos hA))).smul continuous_id.continuousOn

lemma traceRadial_neg (A : M) : traceRadial (-A) = -traceRadial A := by
  simp only [traceRadial,CFC.abs_neg,smul_neg]

end TraceSphere
end BorsukNine

end OAI
