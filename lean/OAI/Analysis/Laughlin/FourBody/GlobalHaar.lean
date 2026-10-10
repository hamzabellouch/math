import OAI.Analysis.Laughlin.FourBody.CopyOperatorHaar
import OAI.Analysis.Laughlin.FourBody.Hermitian
import OAI.Analysis.Laughlin.FourBody.RetainedReconstruction

namespace OAI

namespace Laughlin.Spin
open Rotation Fock
open scoped BigOperators Matrix

theorem physicalFourBodyHaar_retained_sum (Q : ℕ) (hQ : 25 ≤ Q) :
    matrixIntegral sourceHaar
      (conjugateOrbit (fourBodySpinRepresentation Q) ((physicalFourBodyMatrix Q).map Complex.ofReal)) =
    ∑ d : Fin 23, (1 / ((4*Q-1-2*(d.val+1) : ℕ) : ℂ)) •
      fourCopyOperator Q (d.val+1) (by omega)
        (fun r s => physicalFourError Q (d.val+1) (oddPairDeficit r) (oddPairDeficit s)) := by
  classical
  let A : Matrix (FourWedgeIndex Q) (FourWedgeIndex Q) ℂ := matrixIntegral sourceHaar
    (conjugateOrbit (fourBodySpinRepresentation Q) ((physicalFourBodyMatrix Q).map Complex.ofReal))
  let U (d : Fin 23) (r : OddPairLabel (d.val+1)) :
      Matrix (FourWedgeIndex Q) (Fin (fourSpinWeight Q (d.val+1)+1)) ℂ :=
    retainedFourInclusion Q (d.val+1) (by omega) r
  have hr : A = ∑ d : Fin 23, ∑ r : OddPairLabel (d.val+1), A*U d r*(U d r)ᴴ :=
    fourBody_retained_reconstruction Q hQ A (physicalFourBodyHaar_high_column Q)
  have hl : A = ∑ d : Fin 23, ∑ r : OddPairLabel (d.val+1), U d r*(U d r)ᴴ*A := by
    have ha : Aᴴ=A := physicalFourBodyHaar_hermitian Q
    have h := congrArg Matrix.conjTranspose hr
    simpa only [Matrix.conjTranspose_sum,Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose,ha,← Matrix.mul_assoc] using h
  have he (d : Fin 23) (r : OddPairLabel (d.val+1)) :
      U d r*(U d r)ᴴ*A = ∑ s : OddPairLabel (d.val+1),
        ((physicalFourError Q (d.val+1) (oddPairDeficit r) (oddPairDeficit s) : ℂ) /
          ((4*Q-1-2*(d.val+1) : ℕ) : ℂ)) • (U d r*(U d s)ᴴ) := by
    calc
      _ = ∑ e : Fin 23, ∑ s : OddPairLabel (e.val+1),
          U d r*((U d r)ᴴ*A*U e s)*(U e s)ᴴ := by
        conv_lhs => rw [hr]
        simp only [Matrix.mul_sum,Matrix.mul_assoc]
      _ = ∑ s : OddPairLabel (d.val+1),
          U d r*((U d r)ᴴ*A*U d s)*(U d s)ᴴ := by
        apply Finset.sum_eq_single d
        · intro e he hed
          apply Finset.sum_eq_zero
          intro s hs
          have hz : (U d r)ᴴ*A*U e s=0 :=
            fourBody_haar_unequal_spin Q (d.val+1) (e.val+1) (by omega) (by omega)
              (by intro hv; exact hed (Fin.ext (by omega))) r s _
          rw [hz,Matrix.mul_zero,Matrix.zero_mul]
        · simp
      _ = _ := by
        apply Finset.sum_congr rfl
        intro s hs
        have hb : (U d r)ᴴ*A*U d s =
            ((physicalFourError Q (d.val+1) (oddPairDeficit r) (oddPairDeficit s) : ℂ) /
              ((4*Q-1-2*(d.val+1) : ℕ) : ℂ)) • 1 :=
          physical_fourBody_haar_multiplicity Q (d.val+1) hQ (by omega) r s
        rw [hb,Matrix.mul_smul,Matrix.mul_one,Matrix.smul_mul]
  change A = _
  rw [hl]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [he,fourCopyOperator,Finset.smul_sum,smul_smul]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  congr 1
  simp only [div_eq_mul_inv,one_mul,mul_comm]

end Laughlin.Spin

end OAI
