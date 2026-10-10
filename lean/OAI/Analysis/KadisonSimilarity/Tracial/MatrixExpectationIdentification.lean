import OAI.Analysis.KadisonSimilarity.Tracial.ConcreteMatrixTower
import OAI.Analysis.BoundedHochschild.MatrixSystems

namespace OAI

/-! Identification of finite matrix averaging with the constructed normal
conditional expectation, for the relative quantization argument. -/

noncomputable section
namespace KadisonSimilarity

open Generator Generator.Tracial UltrapowerBridge
open scoped ComplexOrder

def matrixSystemOfUnits {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A]
    {n : ℕ} (E : MatrixUnitSystem (Fin n) A) : HochschildMatrixSystems.MatrixSystem A n where
  entry := E.entry
  star_entry := E.star_entry
  entry_mul := E.mul_entry
  sum_diagonal := E.total

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M N : VonNeumannAlgebra H} (υ : TracialRepresentation M)

local instance matrixExpectationClosed : IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed (M : Set (H →L[ℂ] H))
  infer_instance

theorem matrix_average_eq_conditionalExpectation {n : ℕ}
    (E : MatrixUnitSystem (Fin n) M.toStarSubalgebra) (hn : n ≠ 0)
    (x : M.toStarSubalgebra) :
    (matrixSystemOfUnits E).expectation x =
      conditionalExpectation υ E.relativeVonNeumann_le x := by
  let S := matrixSystemOfUnits E
  let ρ := vectorPositiveFunctional M υ.vector
  have htr : ∀ a b, ρ (a * b) = ρ (b * a) := υ.trace_mul_comm
  symm
  apply conditionalExpectation_eq_of_orthogonal υ E.relativeVonNeumann_le
  · apply (E.relativeStar_mem _).mpr
    refine ⟨(S.expectation x).property, fun i j => ?_⟩
    exact congrArg Subtype.val (S.commute_expectation x i j).eq.symm
  · intro a
    have hcomm (i j : Fin n) : Commute (a : M.toStarSubalgebra) (S.entry i j) := by
      apply Subtype.ext
      exact ((E.relativeStar_mem (a : M.toStarSubalgebra).val).mp a.property).2 i j |>.symm
    have ha : S.expectation (a : M.toStarSubalgebra) = a := S.expectation_eq_self hn _ hcomm
    change ρ ((a : M.toStarSubalgebra) * (x - S.expectation x)) = 0
    rw [mul_sub, map_sub, ← S.trace_adjoint ρ htr, ha, sub_self]

theorem matrix_preGNS_norm_sq (x : M.toStarSubalgebra) :
    ‖(vectorPositiveFunctional M υ.vector).toPreGNS x‖ ^ 2 = υ.norm₂ x ^ 2 := by
  rw [HochschildMatrixSystems.MatrixSystem.norm_sq, norm₂_sq_trace]
  rfl

theorem matrix_stage_energy_eq (hNM : N ≤ M) (E : FiniteMatrixStage N)
    (x : M.toStarSubalgebra) :
    E.energy υ hNM x =
      ‖(vectorPositiveFunctional M υ.vector).toPreGNS
        ((matrixSystemOfUnits (E.units.map (coordinateInclusion hNM))).expectation x)‖ ^ 2 := by
  rw [matrix_preGNS_norm_sq, matrix_average_eq_conditionalExpectation υ _
    (Nat.ne_of_gt E.positive)]
  rfl

end KadisonSimilarity

end

end OAI
