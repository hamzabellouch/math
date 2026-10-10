import OAI.Analysis.KadisonKastler.HilbertSumFieldAction
import OAI.Analysis.KadisonKastler.CentralBlockDecomposition

namespace OAI

/-! # Central coordinate projections from the two actual field actions -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {X K : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
  [∀ n, NormedAddCommGroup (K n)] [∀ n, InnerProductSpace ℂ (K n)]
  [∀ n, CompleteSpace (K n)] (μ : ∀ n, Measure (X n))

local notation "L" => fun n => Lp (K n) 2 (μ n)

def HasHilbertSumFields (A : VonNeumannAlgebra (lp L 2)) : Prop :=
  ∀ T ∈ A, ∃ F : ∀ n, X n → K n →L[ℂ] K n,
    ∀ (f : lp L 2) n, T f n =ᵐ[μ n] fun x => F n x (f n x)

theorem hilbertSumProjection_mem_of_commutant_fields (A : VonNeumannAlgebra (lp L 2))
    (hA : HasHilbertSumFields μ A.commutant) (n : ℕ) : hilbertSumProjection n ∈ A := by
  rw [← A.commutant_commutant]
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro S hS
  obtain ⟨F, hF⟩ := hA S hS
  exact (hilbertSum_field_commutes_projection μ S F hF n).symm

theorem hilbertSumProjection_central_of_fields (A : VonNeumannAlgebra (lp L 2))
    (hA : HasHilbertSumFields μ A) (hA' : HasHilbertSumFields μ A.commutant) (n : ℕ) :
    hilbertSumProjection n ∈ A ∧ hilbertSumProjection n ∈ A.commutant := by
  refine ⟨hilbertSumProjection_mem_of_commutant_fields μ A hA' n, ?_⟩
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro T hT
  obtain ⟨F, hF⟩ := hA T hT
  exact (hilbertSum_field_commutes_projection μ T F hF n).symm

theorem blockAlgebraDecomposition_of_field_actions (A : VonNeumannAlgebra (lp L 2))
    (hA : HasHilbertSumFields μ A) (hA' : HasHilbertSumFields μ A.commutant) :
    BlockAlgebraDecomposition
      (fun n => isometricCornerAlgebra (hilbertSumInclusion (E := L) n) A
        (hilbertSumProjection_mem_of_commutant_fields μ A hA' n)) A := by
  exact blockAlgebraDecomposition_of_central_coordinates A
    (hilbertSumProjection_central_of_fields μ A hA hA')

end

end KadisonKastler

end OAI
