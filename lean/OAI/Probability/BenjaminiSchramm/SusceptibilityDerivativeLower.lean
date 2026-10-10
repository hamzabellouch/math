import OAI.Probability.BenjaminiSchramm.SmallWalkKernel

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem susceptibility_derivative_nonneg [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp0 : 0 < (p : ℝ)) (hp : p < pc G) (x : V) :
    0 ≤ deriv (realSusceptibility G x) p := by
  rw [(hasDerivAt_realSusceptibility G hloc hqt p hp0 hp x).deriv]
  exact tsum_nonneg (fun y => russoSlope_nonneg G x y p p.2.2)

theorem susceptibility_derivative_lower_of_kernel [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp0 : 0 < (p : ℝ)) (hp : p < pc G)
    (T K : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G (pc G) T)
    (hK : PositiveRealMatrix K) (d M : ℕ) (hd : ∀ a, degree G a ≤ d)
    (hrow : ∀ a, ∑' b, ennMatrixCoeff K a b = 1)
    (hsupport : ∀ a b, b ∉ reachBall G a M → ennMatrixCoeff K a b = 0)
    (c C : ℝ) (hc : 0 ≤ c) (hC : 0 ≤ C) (x : V)
    (hmin : ∀ b, c * susceptibility G p x ≤ susceptibility G p b)
    (hmax : ∀ b, susceptibility G p b ≤ C * susceptibility G p x)
    (hsmall : C * (‖T‖^3 * ‖K‖) ≤ c/2) :
    (c/2) * (susceptibility G p x)^2 ≤
      (p : ℝ)^(-(M : ℤ)) * ((d+1)^M : ℕ) * (1 - (p : ℝ)) *
        deriv (realSusceptibility G x) p := by
  have hχ := susceptibility_nonneg G p x
  have hder := susceptibility_derivative_nonneg G hloc hqt p hp0 hp x
  have hl := kernelExteriorPotential_lower_of_critical G hloc hqt p hp T K hT hK hrow
    (ENNReal.ofReal (c * susceptibility G p x)) (ENNReal.ofReal (C * susceptibility G p x))
    (fun b => ENNReal.ofReal_le_ofReal (hmin b))
    (fun b => ENNReal.ofReal_le_ofReal (hmax b)) x
  have hu := kernelExteriorPotential_le_derivative G hloc hqt p hp0 hp d hd M
    (ennMatrixCoeff K) hrow hsupport x
  have hh := hl.trans (add_le_add hu le_rfl)
  have hr := ENNReal.toReal_mono (by finiteness) hh
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)] at hr
  simp only [ENNReal.toReal_mul,ENNReal.toReal_ofReal
    (mul_nonneg hc hχ),ENNReal.toReal_ofReal (mul_nonneg hC hχ),
    ENNReal.toReal_ofReal hχ,ENNReal.toReal_ofReal (zpow_nonneg p.2.1 _),
    ENNReal.toReal_natCast,ENNReal.toReal_ofReal (sub_nonneg.mpr p.2.2),
    ENNReal.toReal_ofReal hder,ENNReal.toReal_ofReal
      (mul_nonneg (pow_nonneg (norm_nonneg T) _) (norm_nonneg K))] at hr
  have he := mul_le_mul_of_nonneg_right hsmall (sq_nonneg (susceptibility G p x))
  nlinarith

end Percolation.BenjaminiSchramm

end OAI
