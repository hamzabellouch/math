import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCommonTauBound
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCoreCoordinates
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaVoronoiScale

namespace OAI

/-! The concrete dual coefficient after free-cube removal. Its support
and the required ramified coefficient bound are proved from the actual
three-cusp arithmetic formulas. The summation identity is separate. -/
noncomputable section
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

def CubicThetaCoreSupport (r : Eisenstein) (n : MetaplecticDualArgument) : Prop :=
  ∃ R : CubicThetaCoordinates n.val, ∃ k : ℕ, R.cubePart∣r^k

def cubicThetaCoreCoefficient (r : Eisenstein) (n : MetaplecticDualArgument) : ℂ :=
  if CubicThetaCoreSupport r n then cubicThetaCommonTau n.val else 0

lemma CubicThetaCoordinates.metaplectic_frequency {n : Eisenstein}
    (R : CubicThetaCoordinates n) (hn : n≠0) :
    metaplecticFrequency ⟨n,hn⟩=traceLambda^((R.order:ℤ)-1)*(R.unit:Eisenstein)*
      (R.squarefreePart:ℂ)*(R.cubePart:ℂ)^3 := by
  have hp : traceLambda^((R.order:ℤ)-1)*traceLambda=traceLambda^R.order := by
    calc
      _ = traceLambda^((R.order:ℤ)-1)*traceLambda^(1:ℤ) := by rw [zpow_one]
      _ = _ := by rw [←zpow_add₀ traceLambda_ne_zero,sub_add_cancel,zpow_natCast]
  apply mul_right_cancel₀ traceLambda_ne_zero
  rw [metaplecticFrequency,div_mul_cancel₀ _ traceLambda_ne_zero]
  calc
    _ = (R.unit:Eisenstein)*traceLambda^R.order*
        (R.squarefreePart:ℂ)*(R.cubePart:ℂ)^3 := by
      change (n:ℂ)=_
      conv_lhs => rw [R.numerator_eq]
      push_cast
      rw [lambdaE_coe]
      ring
    _ = _ := by rw [←hp]; ring

theorem cubicThetaCoreCoefficient_bounds :
    MetaplecticCoefficientBounds cubicThetaCoreCoefficient := by
  refine ⟨27,by norm_num,?_⟩
  intro r hr _hs n hne
  have hs : CubicThetaCoreSupport r n := by
    by_contra h
    simp only [cubicThetaCoreCoefficient,ite_eq_right h,zero_mul,ne_eq,not_true_eq_false] at hne
  obtain ⟨R,k,hk⟩ := hs
  let h := primarySmallPart r R.squarefreePart
  let w := primaryOutsidePart r R.squarefreePart
  have hh : primary h := primarySmallPart_primary r R.squarefree_primary
  have hw : primary w := primaryOutsidePart_primary r R.squarefree_primary
  have hc : h*w=R.squarefreePart := primary_small_outside_mul r R.squarefree_primary
  refine ⟨(R.order:ℤ)-1,R.unit,h,R.cubePart,w,by omega,hh,R.cube_primary,hw,
    cubicTheta_primarySmallPart_supported (primary_ne_zero hr) R.squarefree_primary,
    ⟨k,hk⟩,primaryOutsidePart_coprime R.squarefree_primary (primary_ne_zero hr),?_,?_,?_⟩
  · rw [hc]
    exact R.squarefree
  · have he := R.metaplectic_frequency n.property
    rw [←hc] at he
    simpa only [Subalgebra.coe_mul,mul_assoc] using he
  · rw [cubicThetaCoreCoefficient,ite_eq_left ⟨R,k,hk⟩]
    conv_lhs => rw [R.numerator_eq]
    exact cubicThetaCommonTau_coordinate_bound R.unit R.order R.squarefree_primary
      R.cube_primary R.squarefree

end CubicFirstMoment

end

end OAI
