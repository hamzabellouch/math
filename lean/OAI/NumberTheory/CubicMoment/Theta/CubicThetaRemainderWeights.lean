import OAI.NumberTheory.CubicMoment.Theta.CubicThetaTailCoordinates
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaMassPushforward

namespace OAI

/-! A summable majorant on the actual Fourier lattice, with its full mass bounded. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace CubicFirstMoment

def cubicThetaPrimaryDerivativeWeight (p : CubicThetaIntegerPoint) : ℝ :=
  ((9/2:ℝ)*Real.pi)*(if p=(0,0) then 0 else cubicThetaPrimaryTailMass p)

def cubicThetaRamifiedDerivativeWeight (p : CubicThetaIntegerPoint) : ℝ :=
  (27*Real.pi)*(if p=(0,0) then 0 else cubicThetaRamifiedTailMass p)

lemma cubicThetaPrimaryDerivativeWeight_nonneg (p : CubicThetaIntegerPoint) :
    0≤cubicThetaPrimaryDerivativeWeight p := by
  unfold cubicThetaPrimaryDerivativeWeight
  apply mul_nonneg (by positivity)
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (cubicThetaQuadratic_nonneg _ _) (Real.exp_pos _).le

lemma cubicThetaRamifiedDerivativeWeight_nonneg (p : CubicThetaIntegerPoint) :
    0≤cubicThetaRamifiedDerivativeWeight p := by
  unfold cubicThetaRamifiedDerivativeWeight
  apply mul_nonneg (by positivity)
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (cubicThetaQuadratic_nonneg _ _) (Real.exp_pos _).le

lemma cubicThetaPrimaryDerivativeWeight_mass :
    Summable cubicThetaPrimaryDerivativeWeight ∧
    (∑' p,cubicThetaPrimaryDerivativeWeight p)<((9/2:ℝ)*Real.pi)*(13/200) := by
  have h := cubicThetaPrimary_coordinate_mass
  refine ⟨h.1.mul_left _,?_⟩
  change (∑' p,((9/2:ℝ)*Real.pi)*(if p=(0,0) then 0 else cubicThetaPrimaryTailMass p))<_
  rw [tsum_mul_left]
  exact mul_lt_mul_of_pos_left h.2 (by positivity)

lemma cubicThetaRamifiedDerivativeWeight_mass :
    Summable cubicThetaRamifiedDerivativeWeight ∧
    (∑' p,cubicThetaRamifiedDerivativeWeight p)<(27*Real.pi)*(9/2000) := by
  have h := cubicThetaRamified_coordinate_mass
  refine ⟨h.1.mul_left _,?_⟩
  change (∑' p,(27*Real.pi)*(if p=(0,0) then 0 else cubicThetaRamifiedTailMass p))<_
  rw [tsum_mul_left]
  exact mul_lt_mul_of_pos_left h.2 (by positivity)

def cubicThetaPositiveRemainderWeight : Eisenstein → ℝ :=
  cubicThetaMassPushforward (fun p => lambdaE*cubicThetaPrimaryCoordinate p)
    cubicThetaPrimaryDerivativeWeight

def cubicThetaNegativeRemainderWeight : Eisenstein → ℝ :=
  cubicThetaMassPushforward (fun p => -lambdaE*cubicThetaPrimaryCoordinate p)
    cubicThetaPrimaryDerivativeWeight

def cubicThetaHighRemainderWeight : Eisenstein → ℝ :=
  cubicThetaMassPushforward (fun p => lambdaE^3*cubicThetaOrdinaryCoordinate p)
    cubicThetaRamifiedDerivativeWeight

def cubicThetaRemainderWeight (n : Eisenstein) : ℝ :=
  cubicThetaPositiveRemainderWeight n+cubicThetaNegativeRemainderWeight n+
    cubicThetaHighRemainderWeight n

lemma cubicThetaRemainderWeight_properties :
    Summable cubicThetaRemainderWeight ∧ (∀ n,0≤cubicThetaRemainderWeight n) ∧
    (∑' n,cubicThetaRemainderWeight n)<5/2 := by
  have hp := cubicThetaMassPushforward_properties
    (fun p => lambdaE*cubicThetaPrimaryCoordinate p) cubicThetaPrimaryDerivativeWeight
    cubicThetaPrimaryDerivativeWeight_nonneg cubicThetaPrimaryDerivativeWeight_mass.1
  have hn := cubicThetaMassPushforward_properties
    (fun p => -lambdaE*cubicThetaPrimaryCoordinate p) cubicThetaPrimaryDerivativeWeight
    cubicThetaPrimaryDerivativeWeight_nonneg cubicThetaPrimaryDerivativeWeight_mass.1
  have hh := cubicThetaMassPushforward_properties
    (fun p => lambdaE^3*cubicThetaOrdinaryCoordinate p) cubicThetaRamifiedDerivativeWeight
    cubicThetaRamifiedDerivativeWeight_nonneg cubicThetaRamifiedDerivativeWeight_mass.1
  refine ⟨(hp.1.add hn.1).add hh.1,fun n => add_nonneg (add_nonneg (hp.2.2.1 n)
    (hn.2.2.1 n)) (hh.2.2.1 n),?_⟩
  change (∑' n : Eisenstein, ((cubicThetaPositiveRemainderWeight n+
    cubicThetaNegativeRemainderWeight n)+cubicThetaHighRemainderWeight n))<5/2
  simp only [cubicThetaPositiveRemainderWeight,cubicThetaNegativeRemainderWeight,cubicThetaHighRemainderWeight]
  rw [(hp.1.add hn.1).tsum_add hh.1,hp.1.tsum_add hn.1,hp.2.1,hn.2.1,hh.2.1]
  have hP := cubicThetaPrimaryDerivativeWeight_mass.2
  have hH := cubicThetaRamifiedDerivativeWeight_mass.2
  have hpi := Real.pi_lt_d2
  linarith

end CubicFirstMoment

end

end OAI
