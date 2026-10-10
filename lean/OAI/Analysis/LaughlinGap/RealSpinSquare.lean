import Mathlib
import OAI.Analysis.LaughlinGap.PhysicalSpinSpectrum
import OAI.Analysis.LaughlinGap.ThreeBounds

namespace OAI

/-! Real Spin Square. -/

noncomputable section


namespace LaughlinGap
open scoped BigOperators
lemma matrixLift_reindex {ι κ E : Type*} [Fintype ι] [Fintype κ]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (e : ι ≃ κ) (B : κ → Module.End ℂ E) (A : Matrix κ κ ℂ) :
    matrixLift (fun i => B (e i)) (fun i j => A (e i) (e j)) = matrixLift B A := by
  simp only [matrixLift, LinearMap.coe_mk, AddHom.coe_mk]
  have hh (i : κ) : (∑ j : ι, A i (e j) • ((B i).adjoint * B (e j))) =
      ∑ j : κ, A i j • ((B i).adjoint * B j) := e.sum_comp (fun j : κ => A i j • ((B i).adjoint * B j))
  simp only [hh]
  exact e.sum_comp (fun i : κ => ∑ j : κ, A i j • ((B i).adjoint * B j))
end LaughlinGap

namespace LaughlinGap.RealOccupation
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open Averaging Spin Occupation

@[simp] lemma complexify_physicalTriple (Q : ℕ) (a : Fin (2*Q-2+1) × Fin (Q+1)) :
    complexify (physicalTriple Q a) = Occupation.annihilation a.2 * Occupation.localPair (Q+1) Q a.1.val := by
  simp [physicalTriple, productFamily]

lemma complexify_three_lift {Q : ℕ} (hQ : 2 ≤ Q)
    (A : Matrix (Fin (2*Q-2+1) × Fin (Q+1)) (Fin (2*Q-2+1) × Fin (Q+1)) ℝ) :
    complexify (lift (physicalTriple Q) A) =
      exteriorLift (tripleWedgeMatrix (physicalPairForms Q) *
        (Matrix.of (fun i j => (A (physicalThreeIndexEquiv hQ i) (physicalThreeIndexEquiv hQ j) : ℂ)) :
          Matrix (Fin (2*Q-1) × Fin (Q+1)) (Fin (2*Q-1) × Fin (Q+1)) ℂ) *
        (tripleWedgeMatrix (physicalPairForms Q)).conjTranspose) := by
  rw [complexify_lift, exteriorLift, matrixLift_columns]
  have he (i : Fin (2*Q-1) × Fin (Q+1)) :
      contractCombination basisContraction (fun a => tripleWedgeMatrix (physicalPairForms Q) a i) =
      complexify (physicalTriple Q (physicalThreeIndexEquiv hQ i)) := by
    rw [show (fun a => tripleWedgeMatrix (physicalPairForms Q) a i) =
      (tripleWedgeColumn (physicalPairForms Q i.1) i.2 : BasisLabel (Q+1) 3 → ℂ) from rfl]
    change exteriorContraction (tripleWedgeColumn (physicalPairForms Q i.1) i.2) = _
    rw [tripleWedgeColumn_contraction, physicalPair_contraction, complexify_physicalTriple]
    rfl
  simp only [he]
  exact (matrixLift_reindex (physicalThreeIndexEquiv hQ)
    (fun a => complexify (physicalTriple Q a)) (A.map (algebraMap ℝ ℂ))).symm

lemma physicalThreeProjection_real {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    (Matrix.of (fun i j => ((tensorProjection (show z ≤ min (2*Q-2) Q by omega))
      (physicalThreeIndexEquiv hQ i) (physicalThreeIndexEquiv hQ j) : ℂ))) =
      physicalThreeProjection hQ z := by
  ext i j
  simp [tensorProjection_eq, physicalThreeProjection, physicalThreeRankOne,
    physicalThreeVector, Matrix.vecMulVec_apply, Matrix.sum_apply]

@[simp] lemma complexify_threeSpinLift {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    complexify (threeSpinLift hQ hz) = physicalSpinThreeLift hQ z := by
  rw [threeSpinLift, complexify_three_lift hQ, physicalThreeProjection_real hQ hz]
  rfl

lemma threeSpinLift_null {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q) (hn : z=0 ∨ z=1 ∨ z=3) :
    threeSpinLift hQ hz = 0 := by
  apply complexify_injective
  rw [map_zero, complexify_threeSpinLift, physicalSpinThreeLift,
    physicalThreeProjection_wedge_null hQ hz hn, Matrix.zero_mul, map_zero]

noncomputable def fourTarget (Q : ℕ) : FockMatrix (Q+1) :=
  ∑ p : Fin (2*Q-1), ∑ q : Fin (2*Q-1),
    (physicalPair Q q.val * physicalPair Q p.val).transpose *
      (physicalPair Q q.val * physicalPair Q p.val)

lemma fourTarget_positive (Q : ℕ) : (fourTarget Q).PosSemidef :=
  Matrix.posSemidef_sum _ fun _ _ => Matrix.posSemidef_sum _ fun _ _ => transpose_square_positive _

@[simp] lemma complexify_fourTarget (Q : ℕ) :
    complexify (fourTarget Q) = exteriorLift (pairWedgeMatrix (physicalPairForms Q) *
      (pairWedgeMatrix (physicalPairForms Q)).conjTranspose) := by
  rw [← pairFourTerm_eq_lift]
  simp [fourTarget, pairFourTerm, physicalPair_contraction, adjoint_mul]

theorem physical_spin_square_real {Q : ℕ} (hQ : 2 ≤ Q) :
    physicalHamiltonian Q * physicalHamiltonian Q = physicalHamiltonian Q +
      (∑ z : Fin (Q+1), (threeBodyGramCoefficient Q z.val) •
        threeSpinLift hQ (Nat.le_of_lt_succ z.isLt)) + fourTarget Q := by
  apply complexify_injective
  simp only [map_mul, map_add, map_sum, map_smul, complexify_physicalHamiltonian,
    complexify_threeSpinLift, complexify_fourTarget]
  rw [physical_spin_square hQ]
  congr 2
  let e : Fin (min (2*Q-2) Q+1) ≃ Fin (Q+1) := finCongr (by omega)
  have he := e.sum_comp (fun z : Fin (Q+1) =>
    (threeBodyGramCoefficient Q z.val : ℂ) • physicalSpinThreeLift hQ z.val)
  exact he

end LaughlinGap.RealOccupation

end

end OAI
