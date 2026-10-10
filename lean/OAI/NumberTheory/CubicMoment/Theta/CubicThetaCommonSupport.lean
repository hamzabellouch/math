import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCommonCubeScaling
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimaryPowerCoordinates

namespace OAI

/-! The actual three-cusp coefficient has squarefree-times-cube support.
This is proved for the constructed cusps, including their ramified shifts. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaArithmetic_zero_of_no_primary_coordinates {h : Eisenstein}
    (hh : primary h)
    (hn : ¬∃ c d : Eisenstein, primary c ∧ primary d ∧ Squarefree c ∧ h=c*d^3)
    (e : Eisensteinˣ) (k : ℕ) :
    cubicThetaArithmeticCoefficient ((e:Eisenstein)*lambdaE^k*h)=0 := by
  unfold cubicThetaArithmeticCoefficient
  apply dite_eq_right
  exact fun he => hn ((cubicThetaCoordinates_primary_power_iff hh e k).mp he)

lemma cubicThetaCommon_zero_of_no_primary_coordinates {h : Eisenstein}
    (hh : primary h)
    (hn : ¬∃ c d : Eisenstein, primary c ∧ primary d ∧ Squarefree c ∧ h=c*d^3)
    (e : Eisensteinˣ) (k : ℕ) :
    cubicThetaCommonCuspCoefficient ((e:Eisenstein)*lambdaE^k*h)=0 := by
  have hbase : cubicThetaArithmeticCoefficient (-((e:Eisenstein)*lambdaE^k*h))=0 := by
    simpa only [Units.val_neg,neg_mul] using
      cubicThetaArithmetic_zero_of_no_primary_coordinates hh hn (-e) k
  have hshift : cubicThetaArithmeticCoefficient
      (3*(lambdaE*(-((e:Eisenstein)*lambdaE^k*h))))=0 := by
    have he : 3*(lambdaE*(-((e:Eisenstein)*lambdaE^k*h)))=
        (e:Eisenstein)*lambdaE^(k+3)*h := by
      rw [pow_add,pow_succ,lambdaE_sq]
      ring
    rw [he]
    exact cubicThetaArithmetic_zero_of_no_primary_coordinates hh hn e (k+3)
  have hc (j : ℤ) :
      cubicThetaActualCuspCoefficient j (-((e:Eisenstein)*lambdaE^k*h))=0 := by
    unfold cubicThetaActualCuspCoefficient
    split_ifs
    · exact hbase
    · simp only [cubicThetaShiftedLatticeCoefficient,hshift,mul_zero,ite_self]
  unfold cubicThetaCommonCuspCoefficient
  simp only [hc,star_zero,mul_zero,Finset.sum_const_zero,zero_div]

theorem cubicThetaCommonCuspCoefficient_support {n : Eisenstein} (hn : n≠0)
    (ha : cubicThetaCommonCuspCoefficient n≠0) : Nonempty (CubicThetaCoordinates n) := by
  obtain ⟨e,k,h,hh,he⟩ := unit_ramified_primary_decomposition hn
  obtain ⟨c,d,hc,hd,hs,hcd⟩ :
      ∃ c d : Eisenstein, primary c ∧ primary d ∧ Squarefree c ∧ h=c*d^3 := by
    by_contra hbad
    rw [he,cubicThetaCommon_zero_of_no_primary_coordinates hh hbad] at ha
    exact ha rfl
  exact ⟨{
    unit := e
    order := k
    squarefreePart := c
    cubePart := d
    squarefree_primary := hc
    cube_primary := hd
    squarefree := hs
    numerator_eq := by rw [he,hcd] }⟩

end CubicFirstMoment

end

end OAI
