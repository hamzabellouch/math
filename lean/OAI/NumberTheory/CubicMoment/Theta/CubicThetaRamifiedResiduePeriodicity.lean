import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimaryResidueIdentification
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaObservationScaling

namespace OAI

/-! Exact ramified cube periodicity of the actual arithmetic residue,
deduced from the identified primary residue. -/
noncomputable section
open Set Filter Topology
namespace CubicFirstMoment

theorem cubicThetaRegularizedPrimaryOne_lambda_cube {h : Eisenstein} (hh : h≠0)
    {s : ℂ} (hs : 1<s.re) :
    cubicThetaRegularizedPrimaryOne (lambdaE^3*h) s=cubicThetaRegularizedPrimaryOne h s := by
  have h3 : lambdaE^3*h≠0 := mul_ne_zero (pow_ne_zero _ lambdaE_prime.ne_zero) hh
  have he : cubicThetaRegularizedPrimaryOne (lambdaE^3*h)=ᶠ[𝓝[≠] s]
      cubicThetaRegularizedPrimaryOne h := by
    apply cubicThetaMeromorphic_identity
      (fun z hz => (cubicThetaRegularizedPrimaryOne_analytic h3 z hz).meromorphicAt)
      (fun z hz => (cubicThetaRegularizedPrimaryOne_analytic hh z hz).meromorphicAt)
      (convex_halfSpace_re_gt 1).isPreconnected (z₀:=(4:ℂ)) (by norm_num) hs
    have hn : ∀ᶠ z in 𝓝 (4:ℂ), 3<z.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [nhdsWithin_le_nhds hn] with z hz
    rw [cubicThetaRegularizedPrimaryOne_right h3 hz,cubicThetaRegularizedPrimaryOne_right hh hz,
      cubicThetaPrimaryFourierSeries_lambda_cube]
  exact tendsto_nhds_unique
    (((cubicThetaRegularizedPrimaryOne_analytic h3 s hs).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds).congr' he)
    ((cubicThetaRegularizedPrimaryOne_analytic hh s hs).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)

theorem cubicThetaArithmeticFourierResidue_lambda_cube {h : Eisenstein} (hh : h≠0) :
    cubicThetaArithmeticFourierResidue (lambdaE^3*h) (4/3)=
      cubicThetaArithmeticFourierResidue h (4/3) := by
  rw [←cubicThetaRegularizedPrimaryOne_residue_eq
      (mul_ne_zero (pow_ne_zero _ lambdaE_prime.ne_zero) hh),
    ←cubicThetaRegularizedPrimaryOne_residue_eq hh]
  exact cubicThetaRegularizedPrimaryOne_lambda_cube hh (by norm_num)

theorem cubicThetaArithmeticFourierResidue_trace_support {h : Eisenstein} (hh : h≠0)
    (ht : cubicThetaRamifiedTrace h≠2) :
    cubicThetaArithmeticFourierResidue h (4/3)=0 := by
  have he := cubicThetaArithmeticFourierResidue_ramified_step hh
  rw [cubicThetaArithmeticFourierResidue_lambda_cube hh] at he
  have hz : (cubicThetaRamifiedTrace h-2)*cubicThetaArithmeticFourierResidue h (4/3)=0 := by
    linear_combination -he
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr ht)

theorem cubicThetaArithmeticFourierResidue_lambda_cube_pow {h : Eisenstein} (hh : h≠0) (k : ℕ) :
    cubicThetaArithmeticFourierResidue (lambdaE^(3*k)*h) (4/3)=
      cubicThetaArithmeticFourierResidue h (4/3) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h3 : lambdaE^(3*(k+1))*h=lambdaE^3*(lambdaE^(3*k)*h) := by
      rw [Nat.mul_add,pow_add]
      ring
    rw [h3,cubicThetaArithmeticFourierResidue_lambda_cube
      (mul_ne_zero (pow_ne_zero _ lambdaE_prime.ne_zero) hh),ih]

end CubicFirstMoment

end

end OAI
