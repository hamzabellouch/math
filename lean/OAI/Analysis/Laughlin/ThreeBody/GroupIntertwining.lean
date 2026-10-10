import OAI.Analysis.Laughlin.Spin.Intertwining
import OAI.Analysis.Laughlin.Spin.Specializations
import OAI.Analysis.Laughlin.ThreeBody.SpinProjectors

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix Kronecker

noncomputable def threeCoupledInclusion (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1)) :
    Matrix (PairOrbitalIndex Q) (Fin (coupledWeight Q z.val+1)) ℂ :=
  fun i n => (normalizedCoupledDescendant Q z.val hQ (by omega) n.val i : ℂ)

theorem threeCoupledInclusion_SU2 (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1))
    (g : Rotation.SourceSU2) :
    (Rotation.sourceSpinRepresentation (2*Q-2) g ⊗ₖ Rotation.sourceSpinRepresentation Q g)*
      threeCoupledInclusion Q hQ z =
      threeCoupledInclusion Q hQ z*Rotation.sourceSpinRepresentation (coupledWeight Q z.val) g := by
  have hw : genericCoupledWeight (2*Q-2) Q z.val = coupledWeight Q z.val := by
    unfold genericCoupledWeight coupledWeight
    omega
  have h := genericCoupledInclusion_SU2 (2*Q-2) Q z.val (by omega) (by omega) g
  unfold genericCoupledInclusion at h
  simp only [genericUnitDescendant_threeBody Q z.val _ hQ] at h
  rw [hw] at h
  exact h

theorem threeSpinProjector_complex_factor (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1)) :
    (threeSpinProjector Q hQ z).map Complex.ofReal =
      threeCoupledInclusion Q hQ z*(threeCoupledInclusion Q hQ z)ᴴ := by
  funext i j
  change (↑(∑ s, (coupledBasisMatrix Q hQ * coupledSelector Q z) i s *
    coupledBasisMatrix Q hQ j s) : ℂ) = _
  simp only [coupledSelector,Matrix.mul_diagonal]
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,threeCoupledInclusion,
    Complex.star_def,Complex.conj_ofReal]
  rw [Fintype.sum_sigma]
  simp only [mul_ite,mul_one,mul_zero,ite_mul,zero_mul,Finset.sum_ite_irrel,
    Finset.sum_const_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true,Complex.ofReal_sum,
    Complex.ofReal_mul,coupledBasisMatrix]

end Laughlin.Spin

end OAI
