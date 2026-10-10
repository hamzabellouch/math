import OAI.NumberTheory.CubicMoment.Theta.CubicThetaWeightedTest

namespace OAI

/-! The exact algebraic divergence identity for the hyperbolic density
v^-3 and the three real coordinate directions. -/
noncomputable section
open Set
namespace CubicFirstMoment

def cubicThetaCoordinateLaplacian (f : ℂ × ℝ → ℂ) (p : ℂ × ℝ) : ℂ :=
  (p.2:ℂ)^2*(cubicThetaAxisSecond .x f p+cubicThetaAxisSecond .y f p+
    cubicThetaAxisSecond .height f p)-(p.2:ℂ)*cubicThetaAxisFirst .height f p

def cubicThetaCoordinatePairing (φ f : ℂ × ℝ → ℂ) (p : ℂ × ℝ) : ℂ :=
  star (cubicThetaAxisFirst .x φ p)*cubicThetaAxisFirst .x f p+
    star (cubicThetaAxisFirst .y φ p)*cubicThetaAxisFirst .y f p+
    star (cubicThetaAxisFirst .height φ p)*cubicThetaAxisFirst .height f p

def cubicThetaCoordinateDivergence (k : CubicThetaAxis) (φ f : ℂ × ℝ → ℂ)
    (p : ℂ × ℝ) : ℂ :=
  cubicThetaWeightedTest φ p*cubicThetaAxisSecond k f p+
    cubicThetaAxisFirst k (cubicThetaWeightedTest φ) p*cubicThetaAxisFirst k f p

lemma cubicThetaCoordinateLaplacian_hyperbolic (f : ℂ × ℝ → ℂ) (p : ℂ × ℝ) :
    cubicThetaCoordinateLaplacian f p=cubicThetaHyperbolicOperator
      (fun a b t => f (cubicThetaCartesianPoint a b t)) p.1.re p.1.im p.2 := rfl

lemma cubicThetaGreen_identity (φ f : ℂ × ℝ → ℂ) (hφ : ContDiff ℝ 1 φ)
    (hs : tsupport φ⊆{p : ℂ × ℝ | 0<p.2}) (p : ℂ × ℝ) :
    star (φ p)*cubicThetaCoordinateLaplacian f p/(p.2:ℂ)^3+
      cubicThetaHeightInverse p*cubicThetaCoordinatePairing φ f p=
    cubicThetaCoordinateDivergence .x φ f p+cubicThetaCoordinateDivergence .y φ f p+
      cubicThetaCoordinateDivergence .height φ f p := by
  by_cases hp : 0<p.2
  · simp only [cubicThetaCoordinateDivergence,cubicThetaWeightedTest_axis _ hφ hp,
      cubicThetaHeightInverse_axis _ hp,cubicThetaCoordinatePairing,cubicThetaCoordinateLaplacian,
      cubicThetaWeightedTest,cubicThetaHeightInverse,mul_zero,add_zero]
    have hv : (p.2:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hp.ne'
    push_cast
    field_simp [hv]
    ring
  · have hout : p∉tsupport φ := fun h => hp (hs h)
    have hz : φ p=0 := image_eq_zero_of_notMem_tsupport hout
    have hd (k : CubicThetaAxis) : cubicThetaAxisFirst k φ p=0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hout (cubicThetaAxisFirst_support k φ h))
    have hw : cubicThetaWeightedTest φ p=0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hout (cubicThetaWeightedTest_support φ h))
    have hdw (k : CubicThetaAxis) : cubicThetaAxisFirst k (cubicThetaWeightedTest φ) p=0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hout
        (cubicThetaWeightedTest_support φ (cubicThetaAxisFirst_support k (cubicThetaWeightedTest φ) h)))
    simp only [hz,hd,hw,hdw,cubicThetaCoordinateDivergence,cubicThetaCoordinatePairing,
      star_zero,zero_mul,zero_div,mul_zero,add_zero]

end CubicFirstMoment

end

end OAI
