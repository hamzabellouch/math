import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCommonCubeScaling
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamanujanProduct

namespace OAI

/-! Exact primary-cube scaling of the actual dual coefficient and its
local Ramanujan factor. These are the algebraic inputs to free-cube removal. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

def cubicThetaDualCube (d : Eisenstein) (hd : primary d)
    (n : MetaplecticDualArgument) : MetaplecticDualArgument :=
  ⟨n.val*d^3,mul_ne_zero n.property (pow_ne_zero 3 (primary_ne_zero hd))⟩

lemma cubicThetaFrequency_mul_cube (n d : Eisenstein) :
    cubicThetaFrequency (n*d^3)=cubicThetaFrequency n*(d:ℂ)^3 := by
  unfold cubicThetaFrequency
  push_cast
  ring

lemma cubicThetaLocalCoefficient_cube {r d : Eisenstein} (hr : primary r)
    (hd : primary d) (hcop : IsCoprime d r) (n : MetaplecticDualArgument) :
    metaplecticLocalCoefficient r (cubicThetaDualCube d hd n)=
      metaplecticLocalCoefficient r n := by
  unfold metaplecticLocalCoefficient
  apply Finset.prod_congr rfl
  intro p hp
  have hs := primaryPrimeFactor_spec hr hp
  have hpd : ¬p∣d := fun h => hs.1.2.not_isUnit (hcop.isUnit_of_dvd' h hs.2)
  have he : p∣n.val*d^3 ↔ p∣n.val := by
    constructor
    · intro h
      rcases hs.1.2.dvd_mul.mp h with h | h
      · exact h
      · exact False.elim (hpd (hs.1.2.dvd_of_dvd_pow h))
    · intro h
      exact dvd_mul_of_dvd_left h _
  simp only [cubicThetaDualCube,he]

def cubicThetaCommonTau (n : Eisenstein) : ℂ :=
  (‖cubicThetaFrequency n‖:ℂ)*cubicThetaCommonCuspCoefficient n

lemma cubicThetaCommonTau_cube (d : Eisenstein) (hd : primary d) (n : Eisenstein) :
    cubicThetaCommonTau (n*d^3)=
      (Real.sqrt (norm d):ℂ)*cubicThetaCommonTau n := by
  have hn : ‖(d:ℂ)‖^2=norm d := (Complex.normSq_eq_norm_sq _).symm
  have hp : 0<‖(d:ℂ)‖ := norm_pos_iff.mpr
    (fun he => primary_ne_zero hd (Subtype.ext he))
  have hs : Real.sqrt (norm d)=‖(d:ℂ)‖ := by
    rw [←hn,Real.sqrt_sq (_root_.norm_nonneg _)]
  unfold cubicThetaCommonTau
  rw [cubicThetaFrequency_mul_cube,norm_mul,norm_pow,
    cubicThetaCommonCuspCoefficient_primaryCube d hd,hs,←hn]
  push_cast
  field_simp

end CubicFirstMoment

end

end OAI
