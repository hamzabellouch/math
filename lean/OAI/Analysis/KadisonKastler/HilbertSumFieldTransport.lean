import OAI.Analysis.KadisonKastler.SpatialConjugacyTransport
import OAI.Analysis.KadisonKastler.HilbertSumFieldAction
import OAI.Analysis.KadisonKastler.RegularTensorGap

namespace OAI

/-! # Moving an operator-field model through its Hilbert coordinates -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {X K : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
  [∀ n, NormedAddCommGroup (K n)] [∀ n, InnerProductSpace ℂ (K n)]
  [∀ n, CompleteSpace (K n)] (μ : ∀ n, Measure (X n))

local notation "L" => fun n => Lp (K n) 2 (μ n)

theorem transported_algebra_field_decompose (U : H ≃ₗᵢ[ℂ] lp L 2)
    (A : VonNeumannAlgebra H) (P : ∀ n, X n → VonNeumannAlgebra (K n))
    (hmodel : ∀ T ∈ A, ∃ F : ∀ n, X n → K n →L[ℂ] K n,
      (∀ n v, AEStronglyMeasurable (fun x => F n x v) (μ n)) ∧
      (∀ n, ∀ᵐ x ∂μ n, ‖F n x‖ ≤ ‖T‖) ∧ (∀ n, ∀ᵐ x ∂μ n, F n x ∈ P n x) ∧
      ∀ (f : lp L 2) n, U.conjStarAlgEquiv T f n =ᵐ[μ n] fun x => F n x (f n x)) :
    ∀ T ∈ spatialTransportAlgebra U A, ∃ F : ∀ n, X n → K n →L[ℂ] K n,
      (∀ n v, AEStronglyMeasurable (fun x => F n x v) (μ n)) ∧
      (∀ n, ∀ᵐ x ∂μ n, ‖F n x‖ ≤ ‖T‖) ∧ (∀ n, ∀ᵐ x ∂μ n, F n x ∈ P n x) ∧
      ∀ (f : lp L 2) n, T f n =ᵐ[μ n] fun x => F n x (f n x) := by
  rintro _ ⟨T, hT, rfl⟩
  obtain ⟨F, hm, hn, hF, ha⟩ := hmodel T hT
  refine ⟨F, hm, ?_, hF, ha⟩
  intro n
  change ∀ᵐ x ∂μ n, ‖F n x‖ ≤ ‖U.conjStarAlgEquiv T‖
  simpa only [norm_spatialConjugate] using hn n

theorem transported_commutant_fields_of_field_inclusion (U : H ≃ₗᵢ[ℂ] lp L 2)
    (A : VonNeumannAlgebra H) (P Q : ∀ n, X n → VonNeumannAlgebra (K n))
    (hPQ : ∀ n x, Q n x ≤ (P n x).commutant)
    (hdec : ∀ T ∈ spatialTransportAlgebra U A.commutant,
      ∃ F : ∀ n, X n → K n →L[ℂ] K n,
        (∀ n v, AEStronglyMeasurable (fun x => F n x v) (μ n)) ∧
        (∀ n, ∀ᵐ x ∂μ n, ‖F n x‖ ≤ ‖T‖) ∧ (∀ n, ∀ᵐ x ∂μ n, F n x ∈ Q n x) ∧
        ∀ (f : lp L 2) n, T f n =ᵐ[μ n] fun x => F n x (f n x)) :
    ∀ T ∈ (spatialTransportAlgebra U A).commutant,
      ∃ F : ∀ n, X n → K n →L[ℂ] K n,
        (∀ n, ∀ᵐ x ∂μ n, F n x ∈ (P n x).commutant) ∧
        ∀ (f : lp L 2) n, T f n =ᵐ[μ n] fun x => F n x (f n x) := by
  rw [spatialTransportAlgebra_commutant]
  intro T hT
  obtain ⟨F, _, _, hF, ha⟩ := hdec T hT
  exact ⟨F, fun n => (hF n).mono (fun x hx => hPQ n x hx), ha⟩

end

end KadisonKastler

end OAI
