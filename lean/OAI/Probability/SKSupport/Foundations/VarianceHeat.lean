import Mathlib
import OAI.Probability.SKSupport.Foundations.Const

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma hasDerivAt_scaled_second {g : ℝ → ℝ} (hgc : ContDiff ℝ 2 g)
    (hg : ExponentialBound g) (hg' : ExponentialBound (deriv g))
    (hg'' : ExponentialBound (deriv (deriv g))) (a x : ℝ) :
    HasDerivAt (fun z => scaled z g x) (a*scaled a (deriv (deriv g)) x) a := by
  have hgd : ContDiff ℝ 1 (deriv g) := hgc.deriv'
  have hs := standardGaussian_stein
    (g := fun y => deriv g (x+a*y))
    (g' := fun y => a*deriv (deriv g) (x+a*y))
    (fun y => by
      convert (hgd.differentiable (by norm_num) (x+a*y)).hasDerivAt.comp y
        (((hasDerivAt_id y).const_mul a).const_add x) using 1 <;> first | rfl | simp [mul_comm])
    (integrable_scaled_of_expBound hgd.continuous.measurable hg' a x)
    ((integrable_scaled_of_expBound hgd.continuous_deriv_one.measurable hg'' a x).const_mul a)
    (integrable_mul_scaled_of_expBound hgd.continuous.measurable hg' a x)
  rw [integral_const_mul] at hs
  exact (hasDerivAt_scaled (hgc.of_le (by norm_num)) hg hg' a x).congr_deriv hs

def varianceHeat (t : ℝ) (g : ℝ → ℝ) (x : ℝ) := scaled (Real.sqrt t) g x

lemma varianceHeat_zero (g : ℝ → ℝ) (x : ℝ) : varianceHeat 0 g x = g x := by
  simp [varianceHeat, scaled]

lemma continuous_varianceHeat {g : ℝ → ℝ} (hgc : Continuous g) (hg : ExponentialBound g)
    (x : ℝ) : Continuous (fun t => varianceHeat t g x) :=
  (continuous_scaled hgc hg x).comp Real.continuous_sqrt

lemma varianceHeat_eq_semigroup {g : ℝ → ℝ} (hgm : Measurable g) (h : ℝ≥0) (x : ℝ) :
    varianceHeat h g x = semigroup h g x := (semigroup_eq_scaled hgm h x).symm

lemma hasDerivAt_varianceHeat_pos {g : ℝ → ℝ} (hgc : ContDiff ℝ 2 g)
    (hg : ExponentialBound g) (hg' : ExponentialBound (deriv g))
    (hg'' : ExponentialBound (deriv (deriv g))) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun s => varianceHeat s g x) ((1/2:ℝ)*varianceHeat t (deriv (deriv g)) x) t := by
  have hd := (hasDerivAt_scaled_second hgc hg hg' hg'' (Real.sqrt t) x).comp t
    (Real.hasDerivAt_sqrt (ne_of_gt ht))
  apply hd.congr_deriv
  change (Real.sqrt t*scaled (Real.sqrt t) (deriv (deriv g)) x)*(1/(2*Real.sqrt t)) = _
  dsimp only [varianceHeat]
  field_simp [ne_of_gt (Real.sqrt_pos.mpr ht)]

lemma hasDerivWithinAt_varianceHeat {g : ℝ → ℝ} (hgc : ContDiff ℝ 2 g)
    (hg : ExponentialBound g) (hg' : ExponentialBound (deriv g))
    (hg'' : ExponentialBound (deriv (deriv g))) {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    HasDerivWithinAt (fun s => varianceHeat s g x)
      ((1/2:ℝ)*varianceHeat t (deriv (deriv g)) x) (Set.Ici 0) t := by
  by_cases ht0 : t = 0
  · subst t
    apply hasDerivWithinAt_Ici_of_tendsto_deriv (s := Set.Ioi 0)
    · intro r hr
      exact (hasDerivAt_varianceHeat_pos hgc hg hg' hg'' hr x).differentiableAt.differentiableWithinAt
    · exact (continuous_varianceHeat hgc.continuous hg x).continuousAt.continuousWithinAt
    · exact self_mem_nhdsWithin
    · have hc : Continuous (fun r => (1/2:ℝ)*varianceHeat r (deriv (deriv g)) x) :=
        continuous_const.mul (continuous_varianceHeat
          (show Continuous (deriv (deriv g)) from (show ContDiff ℝ 1 (deriv g) from hgc.deriv').continuous_deriv_one)
          hg'' x)
      apply hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds |>.congr'
      filter_upwards [self_mem_nhdsWithin] with r hr
      exact (hasDerivAt_varianceHeat_pos hgc hg hg' hg'' hr x).deriv.symm
  · exact (hasDerivAt_varianceHeat_pos hgc hg hg' hg'' (lt_of_le_of_ne ht (Ne.symm ht0)) x).hasDerivWithinAt

end ZeroTemperatureSK.Heat

end
end
end
end

end OAI
