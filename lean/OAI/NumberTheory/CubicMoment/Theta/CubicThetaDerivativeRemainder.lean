import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRemainderWeights
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaTailTerm

namespace OAI

/-! The actual arithmetic derivative remainder is dominated by the three
summable coordinate families. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaDerivativeRemainder (n : Eisenstein) : ℂ :=
  if n=lambdaE ∨ n= -lambdaE then 0
  else cubicThetaSeriesTermVertical cubicThetaArithmeticCoefficient 0 1 n

lemma cubicThetaRemainderWeight_components (n : Eisenstein) :
    cubicThetaPositiveRemainderWeight n≤cubicThetaRemainderWeight n ∧
    cubicThetaNegativeRemainderWeight n≤cubicThetaRemainderWeight n ∧
    cubicThetaHighRemainderWeight n≤cubicThetaRemainderWeight n := by
  have hp : 0≤cubicThetaPositiveRemainderWeight n :=
    (cubicThetaMassPushforward_properties _ _ cubicThetaPrimaryDerivativeWeight_nonneg
      cubicThetaPrimaryDerivativeWeight_mass.1).2.2.1 n
  have hn : 0≤cubicThetaNegativeRemainderWeight n :=
    (cubicThetaMassPushforward_properties _ _ cubicThetaPrimaryDerivativeWeight_nonneg
      cubicThetaPrimaryDerivativeWeight_mass.1).2.2.1 n
  have hh : 0≤cubicThetaHighRemainderWeight n :=
    (cubicThetaMassPushforward_properties _ _ cubicThetaRamifiedDerivativeWeight_nonneg
      cubicThetaRamifiedDerivativeWeight_mass.1).2.2.1 n
  unfold cubicThetaRemainderWeight
  constructor
  · linarith
  constructor <;> linarith

lemma cubicThetaDerivativeRemainder_bound (n : Eisenstein) :
    ‖cubicThetaDerivativeRemainder n‖≤cubicThetaRemainderWeight n := by
  by_cases he : n=lambdaE ∨ n= -lambdaE
  · simpa only [cubicThetaDerivativeRemainder,ite_eq_left he,norm_zero] using
      cubicThetaRemainderWeight_properties.2.1 n
  rw [cubicThetaDerivativeRemainder,ite_eq_right he]
  by_cases hn : n=0
  · simpa only [cubicThetaSeriesTermVertical,hn,ite_true,norm_zero] using
      cubicThetaRemainderWeight_properties.2.1 0
  by_cases hc : cubicThetaArithmeticCoefficient n=0
  · simpa only [cubicThetaSeriesTermVertical,hn,ite_false,hc,zero_mul,norm_zero] using
      cubicThetaRemainderWeight_properties.2.1 n
  rcases cubicThetaArithmetic_remainder_support (fun h => he (Or.inl h))
    (fun h => he (Or.inr h)) hc with ⟨m,hm,hm1,heq,hc⟩ | ⟨m,hm,heq,hc⟩
  · obtain ⟨p,hp,hpm⟩ := cubicThetaPrimaryCoordinate_exists hm hm1
    have hb := cubicThetaSeriesTermVertical_primary_bound hn
      (cubic_primary_norm_ge_four hm hm1) heq hc
    have hb' : ‖cubicThetaSeriesTermVertical cubicThetaArithmeticCoefficient 0 1 n‖≤
        cubicThetaPrimaryDerivativeWeight p := by
      rw [←hpm,cubicThetaPrimaryCoordinate_norm] at hb
      simpa only [cubicThetaPrimaryDerivativeWeight,ite_eq_right hp,cubicThetaPrimaryTailMass] using hb
    apply hb'.trans
    rcases heq with heq | heq
    · have ht := (cubicThetaMassPushforward_properties
        (fun p => lambdaE*cubicThetaPrimaryCoordinate p) cubicThetaPrimaryDerivativeWeight
        cubicThetaPrimaryDerivativeWeight_nonneg cubicThetaPrimaryDerivativeWeight_mass.1).2.2.2 p
      have he' : lambdaE*cubicThetaPrimaryCoordinate p=n := by rw [hpm,heq]
      rw [he'] at ht
      exact ht.trans (cubicThetaRemainderWeight_components n).1
    · have ht := (cubicThetaMassPushforward_properties
        (fun p => -lambdaE*cubicThetaPrimaryCoordinate p) cubicThetaPrimaryDerivativeWeight
        cubicThetaPrimaryDerivativeWeight_nonneg cubicThetaPrimaryDerivativeWeight_mass.1).2.2.2 p
      have he' : -lambdaE*cubicThetaPrimaryCoordinate p=n := by rw [hpm,heq]
      rw [he'] at ht
      exact ht.trans (cubicThetaRemainderWeight_components n).2.1
  · obtain ⟨p,hp,hpm⟩ := cubicThetaOrdinaryCoordinate_exists hm
    have hb := cubicThetaSeriesTermVertical_ramified_bound hn hm heq hc
    have hb' : ‖cubicThetaSeriesTermVertical cubicThetaArithmeticCoefficient 0 1 n‖≤
        cubicThetaRamifiedDerivativeWeight p := by
      rw [←hpm,cubicThetaOrdinaryCoordinate_norm] at hb
      simpa only [cubicThetaRamifiedDerivativeWeight,ite_eq_right hp,cubicThetaRamifiedTailMass] using hb
    have ht := (cubicThetaMassPushforward_properties
      (fun p => lambdaE^3*cubicThetaOrdinaryCoordinate p) cubicThetaRamifiedDerivativeWeight
      cubicThetaRamifiedDerivativeWeight_nonneg cubicThetaRamifiedDerivativeWeight_mass.1).2.2.2 p
    have he' : lambdaE^3*cubicThetaOrdinaryCoordinate p=n := by rw [hpm,heq]
    rw [he'] at ht
    exact hb'.trans (ht.trans (cubicThetaRemainderWeight_components n).2.2)

lemma cubicThetaDerivativeRemainder_mass :
    Summable cubicThetaDerivativeRemainder ∧ (∑' n,‖cubicThetaDerivativeRemainder n‖)<5/2 := by
  have hs := Summable.of_nonneg_of_le (fun n => _root_.norm_nonneg (cubicThetaDerivativeRemainder n))
    cubicThetaDerivativeRemainder_bound cubicThetaRemainderWeight_properties.1
  exact ⟨hs.of_norm,(hs.tsum_le_tsum cubicThetaDerivativeRemainder_bound
    cubicThetaRemainderWeight_properties.1).trans_lt cubicThetaRemainderWeight_properties.2.2⟩

end CubicFirstMoment

end

end OAI
