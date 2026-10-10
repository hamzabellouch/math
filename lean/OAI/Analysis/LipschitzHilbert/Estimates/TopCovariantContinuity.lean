import OAI.Analysis.LipschitzHilbert.Packets.TopCovariantPacket
import Mathlib.Analysis.Calculus.ContDiff.Deriv

namespace OAI

/-! Continuity and vertical differentiability of the constructed weighted
packet pair, derived from the original packets and their covariant waves. -/

noncomputable section
namespace LipschitzHilbert

theorem topCovariantFactor_continuous (b R : ℝ) (q : ℕ) :
    Continuous (fun y => topCovariantFactor b R y q) := by
  have hp : ContDiff ℝ 1 (polynomialWeight b R q) := by
    unfold polynomialWeight
    fun_prop
  exact (continuous_const.mul hp.continuous_deriv_one).div hp.continuous
    (fun y => ne_of_gt (zero_lt_one.trans_le (polynomialWeight_one_le _ _ _ _)))

theorem topWeightedWave_jointContinuous (f : ℝ → SchwartzMap ℝ ℂ)
    (a r b R : ℝ) (q : ℕ)
    (hf : Continuous (fun z : ℝ × ℝ => f z.1 z.2)) :
    Continuous (fun z : ℝ × ℝ => topWeightedWave (f z.1) a r b R z.1 q z.2) := by
  simp only [topWeightedWave_apply]
  unfold polynomialWeight
  fun_prop

theorem topCovariantWave_jointContinuous (f df : ℝ → SchwartzMap ℝ ℂ)
    (a r b R : ℝ) (q : ℕ)
    (hf : Continuous (fun z : ℝ × ℝ => f z.1 z.2))
    (hdf : Continuous (fun z : ℝ × ℝ => df z.1 z.2)) :
    Continuous (fun z : ℝ × ℝ => topCovariantWave (f z.1) (df z.1) a r b R z.1 q z.2) := by
  have h1 := topWeightedWave_jointContinuous f a r b R q hf
  have h2 := topWeightedWave_jointContinuous df a r b R q hdf
  have hc : Continuous (fun z : ℝ × ℝ => topCovariantFactor b R z.1 q) :=
    (topCovariantFactor_continuous b R q).comp continuous_fst
  change Continuous (fun z : ℝ × ℝ => (topCovariantFactor b R z.1 q:ℂ)*
    topWeightedWave (f z.1) a r b R z.1 q z.2 +
      topWeightedWave (df z.1) a r b R z.1 q z.2)
  exact ((Complex.continuous_ofReal.comp hc).mul h1).add h2

theorem topWeightedWave_vertical_differentiable (f : ℝ → SchwartzMap ℝ ℂ)
    (a r b R x y : ℝ) (q : ℕ) (hf : DifferentiableAt ℝ (fun t => f t x) y) :
    DifferentiableAt ℝ (fun t => topWeightedWave (f t) a r b R t q x) y := by
  have heq : (fun t => topWeightedWave (f t) a r b R t q x) =
      (fun t => (polynomialWeight a r q x:ℂ)*((polynomialWeight b R q t:ℂ)*f t x)) := by
    funext t
    rw [topWeightedWave_apply]
    push_cast
    ring
  rw [heq]
  exact (((((polynomialWeight_differentiable b R q) y).hasDerivAt.ofReal_comp).mul
    hf.hasDerivAt).const_mul _).differentiableAt

theorem topWeightedWave_covariant_continuous (f df : ℝ → SchwartzMap ℝ ℂ)
    (a r b R frequency : ℝ) (q : ℕ) (hR : 0 < R)
    (hf : Continuous (fun z : ℝ × ℝ => f z.1 z.2))
    (hdf : Continuous (fun z : ℝ × ℝ => df z.1 z.2))
    (hfd : ∀ x y, DifferentiableAt ℝ (fun t => f t x) y)
    (hcov : ∀ x y, (4*R:ℂ)*(deriv (fun t => f t x) y-(frequency:ℂ)*Complex.I*f y x) = df y x) :
    Continuous (fun z : ℝ × ℝ =>
      deriv (fun t => topWeightedWave (f t) a r b R t q z.2) z.1 -
        (frequency:ℂ)*Complex.I*topWeightedWave (f z.1) a r b R z.1 q z.2) := by
  have heq : (fun z : ℝ × ℝ =>
      deriv (fun t => topWeightedWave (f t) a r b R t q z.2) z.1 -
        (frequency:ℂ)*Complex.I*topWeightedWave (f z.1) a r b R z.1 q z.2) =
      (fun z : ℝ × ℝ => (4*R:ℂ)⁻¹*topCovariantWave (f z.1) (df z.1) a r b R z.1 q z.2) := by
    funext z
    rw [← topWeightedWave_covariant f df a r b R z.1 frequency z.2 q
      (hfd z.2 z.1) (hcov z.2 z.1)]
    rw [← mul_assoc, inv_mul_cancel₀, one_mul]
    exact mul_ne_zero (by norm_num) (by exact_mod_cast hR.ne')
  rw [heq]
  exact continuous_const.mul (topCovariantWave_jointContinuous f df a r b R q hf hdf)

end LipschitzHilbert

end

end OAI
