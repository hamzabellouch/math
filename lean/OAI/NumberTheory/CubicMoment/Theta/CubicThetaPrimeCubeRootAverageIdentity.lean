import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootCriticalSquare

namespace OAI

/-! Saturation of the actual trace bound identifies the zero-frequency
residue with its once-cubic dilation. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaArithmeticResidue_average_identity {p : Eisenstein} (hp : primaryPrime p) :
    (norm p:ℂ) • cubicThetaPrimeCubeRootFourierL2 hp 0
      (cubicThetaPrimeCubeRootLiftL2 hp cubicThetaArithmeticResidueL2)=
    cubicThetaPrimeCubeRootDilationL2 hp cubicThetaArithmeticResidueL2 := by
  let P := cubicThetaPrimeCubeRootFourierL2 hp 0
    (cubicThetaPrimeCubeRootLiftL2 hp cubicThetaArithmeticResidueL2)
  let A := cubicThetaPrimeCubeRootDilationL2 hp cubicThetaArithmeticResidueL2
  let N := ‖cubicThetaArithmeticResidueL2‖^2
  have h1 : ¬p∣(1:Eisenstein) := fun hd => hp.2.not_isUnit (isUnit_iff_dvd_one.mpr hd)
  have hn := cubicThetaPrimeCubeRoot_norm_balance hp 1 h1 cubicThetaArithmeticResidueL2
  rw [cubicThetaArithmeticResidue_square_projection_zero hp 1 h1,norm_zero,
    zero_pow (by decide : 2≠0),mul_zero,add_zero] at hn
  have hnP : ‖(norm p:ℂ) • P‖^2=N := by
    rw [norm_smul,Complex.norm_of_nonneg (norm_nonneg p),mul_pow]
    exact hn
  have hnA : ‖A‖^2=N := by
    dsimp only [A,N]
    rw [(cubicThetaPrimeCubeRootDilationL2 hp).norm_map]
  have hi : inner ℂ ((norm p:ℂ) • P) A=(N:ℂ) := by
    rw [inner_smul_left (𝕜:=ℂ) (E:=cubicThetaPrimeCubeRootAutomorphicL2 hp),starRingEnd_apply]
    change star (norm p:ℂ)*inner ℂ P A=(N:ℂ)
    rw [show inner ℂ P A=(norm p:ℂ)⁻¹*(N:ℂ) from
      by simpa only [P,A,N,Complex.ofReal_pow] using
        cubicThetaPrimeCubeRootResidue_average_pairing hp]
    simp only [Complex.star_def,Complex.conj_ofReal]
    rw [mul_inv_cancel_left₀ (Complex.ofReal_ne_zero.mpr (norm_pos_of_ne_zero hp.2.ne_zero).ne')]
  have hs := norm_sub_sq (𝕜:=ℂ) ((norm p:ℂ) • P) A
  rw [hnP,hnA,hi] at hs
  change ‖(norm p:ℂ) • P-A‖^2=N-2*N+N at hs
  have hz : ‖(norm p:ℂ) • P-A‖=0 := by nlinarith [hs]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

end CubicFirstMoment

end

end OAI
