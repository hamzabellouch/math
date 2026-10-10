import OAI.Analysis.Laughlin.ThreeBody.HaarBlocks
import OAI.Analysis.Laughlin.ThreeBody.PhysicalTrace

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix
open Rotation

theorem threeSpinProjector_complex_sum (Q : ℕ) (hQ : 2 ≤ Q) :
    (∑ z : Fin (Q+1), (threeSpinProjector Q hQ z).map Complex.ofReal) = 1 := by
  funext i j
  have h := congrArg Complex.ofReal (congrFun (congrFun (threeSpinProjector_sum Q hQ) i) j)
  simpa only [Matrix.sum_apply,Matrix.map_apply,Complex.ofReal_sum,Matrix.one_apply,
    apply_ite,Complex.ofReal_one,Complex.ofReal_zero] using h

theorem physical_threeBody_haar_normalization (Q : ℕ) (hQ : 2 ≤ Q)
    (M : Matrix (PairOrbitalIndex Q) (PairOrbitalIndex Q) ℂ) :
    matrixIntegral sourceHaar (conjugateOrbit (threeBodySpinRepresentation Q) M) =
      ∑ z : Fin (Q+1),
        (Matrix.trace ((threeSpinProjector Q hQ z).map Complex.ofReal*M)/
          (coupledWeight Q z.val+1 : ℕ)) • (threeSpinProjector Q hQ z).map Complex.ofReal := by
  let H := matrixIntegral sourceHaar (conjugateOrbit (threeBodySpinRepresentation Q) M)
  let R := fun z => (threeSpinProjector Q hQ z).map Complex.ofReal
  have hblock (z w : Fin (Q+1)) : R z*H*R w =
      if z=w then (Matrix.trace (R z*M)/(coupledWeight Q z.val+1 : ℕ)) • R z else 0 := by
    change (threeSpinProjector Q hQ z).map Complex.ofReal*H*
      (threeSpinProjector Q hQ w).map Complex.ofReal = _
    rw [threeSpinProjector_complex_factor,threeSpinProjector_complex_factor]
    have he : threeCoupledInclusion Q hQ z*(threeCoupledInclusion Q hQ z)ᴴ*H*
        (threeCoupledInclusion Q hQ w*(threeCoupledInclusion Q hQ w)ᴴ) =
        threeCoupledInclusion Q hQ z*
          ((threeCoupledInclusion Q hQ z)ᴴ*H*threeCoupledInclusion Q hQ w)*
          (threeCoupledInclusion Q hQ w)ᴴ := by simp only [Matrix.mul_assoc]
    rw [he]
    by_cases hzw : z=w
    · subst w
      rw [ite_eq_left rfl]
      change _ = (Matrix.trace ((threeSpinProjector Q hQ z).map Complex.ofReal*M)/_) • _
      rw [threeBody_haar_diagonal_block,Matrix.mul_smul,Matrix.mul_one,Matrix.smul_mul,
        ← threeSpinProjector_complex_factor]
    · rw [ite_eq_right hzw,threeBody_haar_offdiagonal_block Q hQ z w hzw,Matrix.mul_zero,Matrix.zero_mul]
  calc
    _ = (∑ z, R z)*H*(∑ w, R w) := by
      change H = _
      rw [show (∑ z, R z)=1 from threeSpinProjector_complex_sum Q hQ,Matrix.one_mul,Matrix.mul_one]
    _ = ∑ z, ∑ w, R z*H*R w := by rw [Matrix.sum_mul,Matrix.sum_mul]; simp only [Matrix.mul_sum]
    _ = _ := by simp only [hblock,Finset.sum_ite_eq,Finset.mem_univ,ite_true,R]

theorem complex_trace_mul_real {I : Type*} [Fintype I] (A B : Matrix I I ℝ) :
    Matrix.trace (A.map Complex.ofReal * B.map Complex.ofReal) = ((Matrix.trace (A*B) : ℝ) : ℂ) := by
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.map_apply,
    Complex.ofReal_sum,Complex.ofReal_mul]

theorem physical_threeBody_certificate_haar (Q : ℕ) (hQ : 15 ≤ Q) :
    matrixIntegral sourceHaar (conjugateOrbit (threeBodySpinRepresentation Q)
      ((physicalThreeBodyMatrix Q).map Complex.ofReal)) =
      ∑ z : Fin (Q+1),
        ((physicalThreeBodyTraceFormula Q z.val : ℂ)/(coupledWeight Q z.val+1 : ℕ)) •
          (threeSpinProjector Q (by omega) z).map Complex.ofReal := by
  rw [physical_threeBody_haar_normalization Q (by omega)]
  apply Finset.sum_congr rfl
  intro z hz
  rw [complex_trace_mul_real,source_physical_threeBody_trace_identity Q hQ]

end Laughlin.Spin

end OAI
