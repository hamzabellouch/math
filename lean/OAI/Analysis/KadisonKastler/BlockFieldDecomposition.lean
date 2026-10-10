import OAI.Analysis.KadisonKastler.CornerFieldDecomposition

namespace OAI

/-! # Packaging the simultaneous block and field reconstructions -/

namespace KadisonKastler

open MeasureTheory KadisonSimilarity

noncomputable section

variable {X K : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
  [∀ n, NormedAddCommGroup (K n)] [∀ n, InnerProductSpace ℂ (K n)]
  [∀ n, CompleteSpace (K n)] (μ : ∀ n, Measure (X n))

local notation "L" => fun n => Lp (K n) 2 (μ n)

theorem exists_block_field_decomposition
    (A : VonNeumannAlgebra (lp L 2)) (P : ∀ n, X n → VonNeumannAlgebra (K n))
    (hdec : ∀ T ∈ A, ∃ F : ∀ n, X n → K n →L[ℂ] K n,
      (∀ n v, AEStronglyMeasurable (fun x => F n x v) (μ n)) ∧
      (∀ n, ∀ᵐ x ∂μ n, ‖F n x‖ ≤ ‖T‖) ∧ (∀ n, ∀ᵐ x ∂μ n, F n x ∈ P n x) ∧
      ∀ (f : lp L 2) n, T f n =ᵐ[μ n] fun x => F n x (f n x))
    (hcomm : ∀ S ∈ A.commutant, ∃ G : ∀ n, X n → K n →L[ℂ] K n,
      (∀ n, ∀ᵐ x ∂μ n, G n x ∈ (P n x).commutant) ∧
      ∀ (f : lp L 2) n, S f n =ᵐ[μ n] fun x => G n x (f n x)) :
    ∃ Q : ∀ n, VonNeumannAlgebra (L n), BlockAlgebraDecomposition Q A ∧
      ∀ n, OperatorFieldDecomposition (μ n) (P n) (Q n) := by
  have hAf : HasHilbertSumFields μ A := by
    intro T hT
    obtain ⟨F, _, _, _, ha⟩ := hdec T hT
    exact ⟨F, ha⟩
  have hAc : HasHilbertSumFields μ A.commutant := by
    intro T hT
    obtain ⟨F, _, ha⟩ := hcomm T hT
    exact ⟨F, ha⟩
  let Q := fun n => isometricCornerAlgebra (hilbertSumInclusion (E := L) n) A
    (hilbertSumProjection_mem_of_commutant_fields μ A hAc n)
  refine ⟨Q, blockAlgebraDecomposition_of_field_actions μ A hAf hAc, ?_⟩
  intro n
  exact cornerOperatorFieldDecomposition μ A P hdec hcomm n

end

end KadisonKastler

end OAI
