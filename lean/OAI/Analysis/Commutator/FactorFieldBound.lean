import Mathlib
import OAI.Analysis.Commutator.DiagonalField
import OAI.Analysis.Commutator.FiberCommutator
import OAI.Analysis.Commutator.MatrixField
import OAI.Analysis.Commutator.SeparableFactorMain
import OAI.Analysis.Commutator.UnitaryMainTransport

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology InnerProductSpace

namespace Kadison.Decomposable

variable {Ω : Type*} {H : Type} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H]

theorem matrix_commutator_bound_of_factor_fields
    (Q : Ω → VonNeumannAlgebra H) (hfac : ∀ᵐ a ∂μ,FactorCorner.IsFactor (Q a))
    (T : Ω → H →L[ℂ] H)
    (hT : ∀ ξ,AEStronglyMeasurable (fun a => T a ξ) μ)
    {b d : ℝ} (hb0 : 0≤b) (hd : 0≤d) (hb : ∀ᵐ a ∂μ,‖T a‖≤b)
    (hg : ∀ᵐ a ∂μ,commutatorSeminorm (Q a) (T a)≤d)
    (h : ℕ) (hh : 1≤h) (X : Fin h → Fin h → Ω → H →L[ℂ] H)
    (hX : ∀ i j ξ,AEStronglyMeasurable (fun a => X i j a ξ) μ)
    {c : Fin h → Fin h → ℝ} (hc0 : ∀ i j,0≤c i j)
    (hc : ∀ i j,∀ᵐ a ∂μ,‖X i j a‖≤c i j)
    (hmem : ∀ᵐ a ∂μ,∀ i j,X i j a∈Q a) :
    ‖diagonalAmplification h (operator μ T hT hb)*
        matrixOperator h (fun i j => operator μ (X i j) (hX i j) (hc i j))-
      matrixOperator h (fun i j => operator μ (X i j) (hX i j) (hc i j))*
        diagonalAmplification h (operator μ T hT hb)‖≤
      3122*d*‖matrixOperator h (fun i j => operator μ (X i j) (hX i j) (hc i j))‖ := by
  let D := fun a => diagonalAmplification h (T a)
  let M := fun a => matrixOperator h (fun i j => X i j a)
  let G := matrixOperator h (fun i j => operator μ (X i j) (hX i j) (hc i j))
  have hD := diagonal_field_measurable μ h T hT
  have hM := matrix_field_measurable μ h X hX
  have hDb := diagonal_field_bound μ h T hb
  have hMb := matrix_field_bound μ h X hc
  have hcnonneg : 0≤∑ i,∑ j,c i j :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hc0 i j))
  have hmatrix : ∀ᵐ a ∂μ,‖M a‖≤‖G‖ := by
    apply (operator_norm_le_iff_ae μ M hM hMb (norm_nonneg G)).mp
    rw [←matrix_conjugate μ h X hX hc,UnitaryTransport.conj_norm]
  have hfiber : ∀ᵐ a ∂μ,‖D a*M a-M a*D a‖≤3122*d*‖G‖ := by
    filter_upwards [hfac,hmem,hg,hmatrix] with a hfa hma hga hna
    have hf := uniform_commutator_separable_factor (Q a) hfa (T a) h hh
      (fun i j => X i j a) hma
    exact hf.trans (mul_le_mul (mul_le_mul_of_nonneg_left hga (by norm_num)) hna
      (norm_nonneg _) (mul_nonneg (by norm_num) hd))
  have hn := operator_norm_le μ (fun a => D a*M a-M a*D a)
    (commutator_measurable μ D M hD hM)
    (commutator_field_bound μ D M hb0 hcnonneg hDb hMb)
    (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤3122) hd) (norm_nonneg G)) hfiber
  rw [←operator_commutator μ D M hD hM hb0 hcnonneg hDb hMb] at hn
  change ‖operator μ D hD hDb*operator μ M hM hMb-
    operator μ M hM hMb*operator μ D hD hDb‖≤_ at hn
  rw [←diagonal_conjugate μ h T hT hb,←matrix_conjugate μ h X hX hc,
    ←map_mul,←map_mul,←map_sub,UnitaryTransport.conj_norm] at hn
  exact hn

theorem matrix_commutator_bound_of_countable_factor_fields
    (P : VonNeumannAlgebra (Lp H 2 μ)) (Q : Ω → VonNeumannAlgebra H)
    (hfac : ∀ᵐ a ∂μ,FactorCorner.IsFactor (Q a))
    (T : Ω → H →L[ℂ] H)
    (hT : ∀ ξ,AEStronglyMeasurable (fun a => T a ξ) μ)
    {b : ℝ} (hb0 : 0≤b) (hb : ∀ᵐ a ∂μ,‖T a‖≤b)
    (test : ℕ → Ω → H →L[ℂ] H)
    (ht : ∀ n ξ,AEStronglyMeasurable (fun a => test n a ξ) μ)
    (htb : ∀ n,∀ᵐ a ∂μ,‖test n a‖≤1)
    (htmem : ∀ n,operator μ (test n) (ht n) (htb n)∈P)
    (htdense : ∀ᵐ a ∂μ,∀ A : H →L[ℂ] H,A∈Q a → ‖A‖≤1 →
      ∃ k : ℕ → ℕ,∀ ξ,Tendsto (fun n => test (k n) a ξ) atTop (𝓝 (A ξ)))
    (h : ℕ) (hh : 1≤h) (X : Fin h → Fin h → Ω → H →L[ℂ] H)
    (hX : ∀ i j ξ,AEStronglyMeasurable (fun a => X i j a ξ) μ)
    {c : Fin h → Fin h → ℝ} (hc0 : ∀ i j,0≤c i j)
    (hc : ∀ i j,∀ᵐ a ∂μ,‖X i j a‖≤c i j)
    (hmem : ∀ᵐ a ∂μ,∀ i j,X i j a∈Q a) :
    ‖diagonalAmplification h (operator μ T hT hb)*
        matrixOperator h (fun i j => operator μ (X i j) (hX i j) (hc i j))-
      matrixOperator h (fun i j => operator μ (X i j) (hX i j) (hc i j))*
        diagonalAmplification h (operator μ T hT hb)‖≤
      3122*commutatorSeminorm P (operator μ T hT hb)*
        ‖matrixOperator h (fun i j => operator μ (X i j) (hX i j) (hc i j))‖ :=
  matrix_commutator_bound_of_factor_fields μ Q hfac T hT hb0
    (commutatorSeminorm_nonneg P _) hb
    (seminorm_ae_le μ P Q T hT hb0 hb test ht htb htmem htdense)
    h hh X hX hc0 hc hmem

end Kadison.Decomposable

end

end
end

end OAI
