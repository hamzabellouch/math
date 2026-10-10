import OAI.Analysis.KadisonKastler.DirectIntegralConjugacy
import OAI.Analysis.KadisonKastler.L2LinearFields

namespace OAI

/-! # Reconstructing bounded fields from the commutant

A measurable bounded field in the fiber algebra defines an operator on L².
Actual fields for the commutant show that this operator belongs to the original
von Neumann algebra, by the bicommutant theorem.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (μ : Measure X) (M : X → VonNeumannAlgebra H)
  (A : VonNeumannAlgebra (Lp H 2 μ))

theorem reconstruct_field_of_commutant_fields
    (hcomm : ∀ S ∈ A.commutant, ∃ G : X → H →L[ℂ] H,
      (∀ᵐ x ∂μ, G x ∈ (M x).commutant) ∧ RepresentsOperatorField μ G S)
    (F : X → H →L[ℂ] H) (C : ℝ)
    (hm : ∀ v, AEStronglyMeasurable (fun x => F x v) μ)
    (hn : ∀ᵐ x ∂μ, ‖F x‖ ≤ C) (hF : ∀ᵐ x ∂μ, F x ∈ M x) :
    ∃ T ∈ A, RepresentsOperatorField μ F T := by
  let T := l2LinearFieldMap μ F hm C hn
  have hT : RepresentsOperatorField μ F T :=
    fun f => l2LinearFieldApply_ae μ F hm C hn f
  refine ⟨T, ?_, hT⟩
  rw [← A.commutant_commutant]
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro S hS
  obtain ⟨G, hG, hSG⟩ := hcomm S hS
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [hSG (T f), hT f, hT (S f), hSG f, hG, hF]
    with x hST hTf hTS hSf hGx hFx
  change (S (T f)) x = (T (S f)) x
  rw [hST, hTf, hTS, hSf]
  exact congrArg (fun R : H →L[ℂ] H => R (f x))
    (VonNeumannAlgebra.mem_commutant_iff.mp hGx (F x) hFx).symm

theorem operatorFieldDecomposition_of_commutant_fields
    (hdec : ∀ T ∈ A, ∃ F : X → H →L[ℂ] H,
      (∀ v, AEStronglyMeasurable (fun x => F x v) μ) ∧
      (∀ᵐ x ∂μ, ‖F x‖ ≤ ‖T‖) ∧ (∀ᵐ x ∂μ, F x ∈ M x) ∧
      RepresentsOperatorField μ F T)
    (hcomm : ∀ S ∈ A.commutant, ∃ G : X → H →L[ℂ] H,
      (∀ᵐ x ∂μ, G x ∈ (M x).commutant) ∧ RepresentsOperatorField μ G S) :
    OperatorFieldDecomposition μ M A := by
  refine ⟨hdec, ?_⟩
  intro F C _ hm hn hF
  exact reconstruct_field_of_commutant_fields μ M A hcomm F C hm hn hF

end

end KadisonKastler

end OAI
