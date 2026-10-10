import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCoreArguments
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaVoronoiScale

namespace OAI

/-! Exact conversion from the common theta lattice to the dual lattice.
The fixed dilation by 729 is retained in the transform argument. -/
noncomputable section
namespace CubicFirstMoment

lemma complexAngular_mul (ℓ : ℤ) (z w : ℂ) :
    complexAngular ℓ (z*w)=complexAngular ℓ z*complexAngular ℓ w := by
  simp only [complexAngular,norm_mul,Complex.ofReal_mul]
  rw [mul_div_mul_comm,mul_zpow]

lemma cubicThetaCircleOrder_neg (rev : Bool) (k : ℕ) :
    cubicThetaCircleOrder rev k = -cubicThetaCircleOrder (!rev) k := by
  cases rev <;> simp [cubicThetaCircleOrder]

lemma cubicTheta_dual_phase (ℓ : ℤ) (n : MetaplecticDualArgument) (d : Eisenstein) :
    theta ℓ (n.val*d^3)=theta ℓ lambdaE*
      complexAngular ℓ ((d:ℂ)^3*metaplecticFrequency n) := by
  have he : ((n.val*d^3:Eisenstein):ℂ)=
      (lambdaE:ℂ)*((d:ℂ)^3*metaplecticFrequency n) := by
    simp only [Subalgebra.coe_mul,Subalgebra.coe_pow,metaplecticFrequency]
    change (n.val:ℂ)*(d:ℂ)^3=traceLambda*((d:ℂ)^3*((n.val:ℂ)/traceLambda))
    field_simp [traceLambda_ne_zero]
  rw [←complexAngular_coe,he,complexAngular_mul,complexAngular_coe]

lemma cubicTheta_dual_norm (n : MetaplecticDualArgument) :
    ‖cubicThetaFrequency n.val‖^2=Complex.normSq (metaplecticFrequency n)/27 := by
  rw [cubicThetaFrequency_sq,cubicTheta_metaplectic_normSq]
  ring

lemma cubicTheta_dual_cube_argument {r : Eisenstein} (hr : primary r)
    (n : MetaplecticDualArgument) (d : Eisenstein) (X : ℝ) :
    cubicThetaDualScale r (X/27)*‖cubicThetaFrequency n.val‖^2*norm d^3=
      (2*Real.pi)^4*Complex.normSq ((d:ℂ)^3*metaplecticFrequency n)*(X/729)/norm r^2 := by
  rw [cubicThetaVoronoi_dual_argument hr,Complex.normSq_mul,map_pow]
  change (2*Real.pi)^4*Complex.normSq (metaplecticFrequency n)*X/(729*norm r^2)*norm d^3=
    (2*Real.pi)^4*(norm d^3*Complex.normSq (metaplecticFrequency n))*(X/729)/norm r^2
  ring

lemma cubicThetaFreeLocalDualTerm_frequency {r : Eisenstein} (hr : primary r)
    (rev : Bool) (k : ℕ) (W : ℝ→ℂ) (σ X : ℝ)
    (x : CubicThetaCoreIndex r × CubicThetaFreeArgument r) :
    cubicThetaFreeLocalDualTerm r rev k W σ X x=
      27*theta (cubicThetaCircleOrder rev k) lambdaE*
        metaplecticDualTerm cubicThetaCoreCoefficient r (cubicThetaCircleOrder (!rev) k)
          W σ (X/729) (cubicThetaCoreFreeArgument r x) := by
  have he := congrArg Subtype.val (cubicThetaFreeCubeJoin_argument r x)
  change cubicThetaCommonNumerator (cubicThetaFreeCubeJoin r x)=
    cubicThetaCommonNumerator x.1.val*(x.2.val:Eisenstein)^3 at he
  unfold cubicThetaFreeLocalDualTerm
  rw [he,show cubicThetaCommonNumerator x.1.val=(cubicThetaCoreArgument x.1).val from rfl]
  change theta _ ((cubicThetaCoreArgument x.1).val*(x.2.val:Eisenstein)^3)*
    (cubicThetaCoreCoefficient r (cubicThetaCoreArgument x.1)*
      metaplecticLocalCoefficient r (cubicThetaCoreArgument x.1))/_*_= _
  rw [cubicTheta_dual_phase,
    cubicTheta_dual_cube_argument hr (cubicThetaCoreArgument x.1) (x.2.val:Eisenstein),
    cubicTheta_dual_norm (cubicThetaCoreArgument x.1)]
  dsimp only [metaplecticDualTerm,cubicThetaCoreFreeArgument]
  rw [ite_eq_left x.2.property]
  simp only [←cubicThetaCircleOrder_neg rev k,Complex.ofReal_mul,Complex.ofReal_div,
    Complex.ofReal_ofNat]
  ring

end CubicFirstMoment

end

end OAI
