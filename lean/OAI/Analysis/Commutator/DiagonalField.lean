import Mathlib
import OAI.Analysis.Commutator.DecomposableAlgebra
import OAI.Analysis.Commutator.L2FiniteSum
import OAI.Analysis.Commutator.MainCommutantDistance
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

omit [CompleteSpace H] in
lemma diagonal_field_measurable (h : ℕ) (T : Ω → H →L[ℂ] H)
    (hm : ∀ ξ,AEStronglyMeasurable (fun a => T a ξ) μ)
    (ξ : PiLp 2 (fun _ : Fin h => H)) :
    AEStronglyMeasurable (fun a => diagonalAmplification h (T a) ξ) μ := by
  classical
  have eqn (a) : diagonalAmplification h (T a) ξ=
      ∑ i,OperatorAmplification.single (Fin h) i (T a (ξ i)) := by
    ext i
    simp [diagonalAmplification_apply,OperatorAmplification.single_apply]
  simp_rw [eqn]
  exact Finset.aestronglyMeasurable_fun_sum _ (fun i _ =>
    (OperatorAmplification.single (Fin h) i).continuous.comp_aestronglyMeasurable (hm (ξ i)))

omit [CompleteSpace H] in
lemma diagonal_field_bound (h : ℕ) (T : Ω → H →L[ℂ] H)
    {b : ℝ} (hb : ∀ᵐ a ∂μ,‖T a‖≤b) :
    ∀ᵐ a ∂μ,‖diagonalAmplification h (T a)‖≤b := by
  filter_upwards [hb] with a ha
  exact (diagonalAmplification_norm_le h (T a)).trans ha

omit [CompleteSpace H] in
lemma assemble_diagonal_ae (h : ℕ) (T : Ω → H →L[ℂ] H)
    (hm : ∀ ξ,AEStronglyMeasurable (fun a => T a ξ) μ)
    {b : ℝ} (hb : ∀ᵐ a ∂μ,‖T a‖≤b)
    (f : PiLp 2 (fun _ : Fin h => Lp H 2 μ)) :
    assemble μ (diagonalAmplification h (operator μ T hm hb) f)=ᵐ[μ]
    fun a => diagonalAmplification h (T a) (assemble μ f a) := by
  have he : ∀ᵐ a ∂μ,∀ i,operator μ T hm hb (f i) a=T a (f i a) :=
    ae_all_iff.mpr (fun i => operator_ae μ _ _ _ (f i))
  filter_upwards [assemble_ae μ (diagonalAmplification h (operator μ T hm hb) f),
    assemble_ae μ f,he] with a ha hf he
  rw [ha,hf]
  ext i
  exact he i

lemma diagonal_conjugate (h : ℕ) (T : Ω → H →L[ℂ] H)
    (hm : ∀ ξ,AEStronglyMeasurable (fun a => T a ξ) μ)
    {b : ℝ} (hb : ∀ᵐ a ∂μ,‖T a‖≤b) :
    (finiteSumEquiv μ).conjStarAlgEquiv (diagonalAmplification h (operator μ T hm hb))=
    operator μ (fun a => diagonalAmplification h (T a))
      (diagonal_field_measurable μ h T hm) (diagonal_field_bound μ h T hb) := by
  apply operator_eq_of_ae_apply
  intro f
  have hh := assemble_diagonal_ae μ h T hm hb ((finiteSumEquiv μ).symm f)
  change (assemble μ (diagonalAmplification h (operator μ T hm hb)
    ((finiteSumEquiv μ).symm f))) =ᵐ[μ] _
  convert hh using 1
  rw [show assemble μ ((finiteSumEquiv μ).symm f)=f from (finiteSumEquiv μ).apply_symm_apply f]

end Kadison.Decomposable

end

end
end

end OAI
