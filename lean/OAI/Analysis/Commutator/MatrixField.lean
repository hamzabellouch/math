import Mathlib
import OAI.Analysis.Commutator.DecomposableAlgebra
import OAI.Analysis.Commutator.L2FiniteSum
import OAI.Analysis.Commutator.MainMatrix
import OAI.Analysis.Commutator.OperatorAmplification

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology InnerProductSpace

namespace Kadison.Decomposable

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
lemma vector_norm_le_sum {ι : Type*} [Fintype ι] (v : PiLp 2 (fun _ : ι => H)) :
    ‖v‖≤∑ i,‖v i‖ := by
  classical
  have he : ∑ i,PiLp.single 2 i (v i)=v := by ext i; simp
  rw [←he]
  convert norm_sum_le (Finset.univ) (fun i => PiLp.single 2 i (v i)) using 1
  simp only [PiLp.norm_single]
  rw [he]

omit [CompleteSpace H] in
lemma matrix_norm_le_sum (h : ℕ) (X : Matrix (Fin h) (Fin h) (H →L[ℂ] H)) :
    ‖matrixOperator h X‖≤∑ i,∑ j,‖X i j‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  calc
    ‖matrixOperator h X x‖≤∑ i,‖matrixOperator h X x i‖ := vector_norm_le_sum _
    _≤∑ i,∑ j,‖X i j‖*‖x‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [matrixOperator_apply]
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro j _
      exact ((X i j).le_opNorm (x j)).trans
        (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le x j) (norm_nonneg _))
    _=(∑ i,∑ j,‖X i j‖)*‖x‖ := by simp only [Finset.sum_mul]

omit [CompleteSpace H] in
lemma matrix_field_measurable (h : ℕ) (X : Fin h → Fin h → Ω → H →L[ℂ] H)
    (hm : ∀ i j ξ,AEStronglyMeasurable (fun a => X i j a ξ) μ)
    (ξ : PiLp 2 (fun _ : Fin h => H)) :
    AEStronglyMeasurable (fun a => matrixOperator h (fun i j => X i j a) ξ) μ := by
  classical
  have eqn (a) : matrixOperator h (fun i j => X i j a) ξ=
      ∑ i,OperatorAmplification.single (Fin h) i (∑ j,X i j a (ξ j)) := by
    ext i
    erw [matrixOperator_apply]
    simp [OperatorAmplification.single_apply]
  simp_rw [eqn]
  apply Finset.aestronglyMeasurable_fun_sum
  intro i _
  exact (OperatorAmplification.single (Fin h) i).continuous.comp_aestronglyMeasurable
    (Finset.aestronglyMeasurable_fun_sum _ (fun j _ => hm i j (ξ j)))

omit [CompleteSpace H] in
lemma matrix_field_bound (h : ℕ) (X : Fin h → Fin h → Ω → H →L[ℂ] H)
    {b : Fin h → Fin h → ℝ} (hb : ∀ i j,∀ᵐ a ∂μ,‖X i j a‖≤b i j) :
    ∀ᵐ a ∂μ,‖matrixOperator h (fun i j => X i j a)‖≤∑ i,∑ j,b i j := by
  filter_upwards [ae_all_iff.mpr (fun i => ae_all_iff.mpr (hb i))] with a ha
  exact (matrix_norm_le_sum h _).trans (Finset.sum_le_sum (fun i _ =>
    Finset.sum_le_sum (fun j _ => ha i j)))

omit [CompleteSpace H] in
lemma assemble_matrix_ae (h : ℕ) (X : Fin h → Fin h → Ω → H →L[ℂ] H)
    (hm : ∀ i j ξ,AEStronglyMeasurable (fun a => X i j a ξ) μ)
    {b : Fin h → Fin h → ℝ} (hb : ∀ i j,∀ᵐ a ∂μ,‖X i j a‖≤b i j)
    (f : PiLp 2 (fun _ : Fin h => Lp H 2 μ)) :
    assemble μ (matrixOperator h (fun i j => operator μ (X i j) (hm i j) (hb i j)) f)=ᵐ[μ]
    fun a => matrixOperator h (fun i j => X i j a) (assemble μ f a) := by
  have he : ∀ᵐ a ∂μ,∀ i j,operator μ (X i j) (hm i j) (hb i j) (f j) a=X i j a (f j a) :=
    ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j => operator_ae μ _ _ _ (f j)))
  have hs : ∀ᵐ a ∂μ,∀ i,(∑ j,operator μ (X i j) (hm i j) (hb i j) (f j)) a=
      ∑ j,operator μ (X i j) (hm i j) (hb i j) (f j) a :=
    ae_all_iff.mpr (fun i => Lp.coeFn_fun_finsetSum _ _)
  filter_upwards [assemble_ae μ (matrixOperator h (fun i j => operator μ (X i j) (hm i j) (hb i j)) f),
    assemble_ae μ f,he,hs] with a ha hf he hs
  rw [ha,hf]
  ext i
  change (matrixOperator h (fun i j => operator μ (X i j) (hm i j) (hb i j)) f i) a=
    matrixOperator h (fun i j => X i j a) (WithLp.toLp 2 (fun i => f i a)) i
  erw [matrixOperator_apply,matrixOperator_apply]
  rw [hs i]
  exact Finset.sum_congr rfl (fun j _ => he i j)

lemma matrix_conjugate (h : ℕ) (X : Fin h → Fin h → Ω → H →L[ℂ] H)
    (hm : ∀ i j ξ,AEStronglyMeasurable (fun a => X i j a ξ) μ)
    {b : Fin h → Fin h → ℝ} (hb : ∀ i j,∀ᵐ a ∂μ,‖X i j a‖≤b i j) :
    (finiteSumEquiv μ).conjStarAlgEquiv
      (matrixOperator h (fun i j => operator μ (X i j) (hm i j) (hb i j)))=
    operator μ (fun a => matrixOperator h (fun i j => X i j a))
      (matrix_field_measurable μ h X hm) (matrix_field_bound μ h X hb) := by
  apply operator_eq_of_ae_apply
  intro f
  have hh := assemble_matrix_ae μ h X hm hb ((finiteSumEquiv μ).symm f)
  change (assemble μ (matrixOperator h (fun i j => operator μ (X i j) (hm i j) (hb i j))
    ((finiteSumEquiv μ).symm f))) =ᵐ[μ] _
  convert hh using 1
  rw [show assemble μ ((finiteSumEquiv μ).symm f)=f from (finiteSumEquiv μ).apply_symm_apply f]

end Kadison.Decomposable

end

end
end

end OAI
