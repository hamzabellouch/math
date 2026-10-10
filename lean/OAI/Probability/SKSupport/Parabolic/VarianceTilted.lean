import Mathlib
import OAI.Probability.SKSupport.Parabolic.UniformTiltedMeanBounds
import OAI.Probability.SKSupport.Foundations.ExponentialBoundLipschitz

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

lemma varianceHeat_eq_semigroup_toNNReal {g : ℝ → ℝ} (hgm : Measurable g) (t x : ℝ) :
    varianceHeat t g x = semigroup (Real.toNNReal t) g x := by
  rw [semigroup_eq_scaled hgm]
  unfold varianceHeat
  have he : Real.sqrt ((Real.toNNReal t:ℝ≥0):ℝ) = Real.sqrt t := by
    simp only [Real.sqrt, Real.toNNReal_coe]
  rw [he]

lemma varianceLogHeat_eq_logSemigroup_toNNReal {f : ℝ → ℝ} (hfm : Measurable f) (c t x : ℝ) :
    varianceLogHeat c t f x = logSemigroup c (Real.toNNReal t) f x := by
  by_cases hc : c = 0
  · simp only [varianceLogHeat, logSemigroup, hc, ↓reduceIte]
    exact varianceHeat_eq_semigroup_toNNReal hfm t x
  · simp only [varianceLogHeat, logSemigroup, hc, ↓reduceIte]
    have hem : Measurable (fun z => Real.exp (c*f z)) := (measurable_const.mul hfm).exp
    rw [varianceHeat_eq_semigroup_toNNReal hem t x]

lemma uniform_logSemigroup_derivative_bounds {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    ∃ C : ℝ≥0, ∀ h : ℝ≥0, ∀ x, |iteratedDeriv (n+1) (logSemigroup c h f) x| ≤ C := by
  by_cases hc0 : c = 0
  · subst c
    obtain ⟨C,hC⟩ := uniform_tiltedMean_bounds (RegularDatum.const 0)
      (LipschitzWith.const (0:ℝ)) hf.deriv_bounded (c := 0) le_rfl n
    refine ⟨C, fun h x => ?_⟩
    have he : logSemigroup 0 h f = semigroup h f := by funext z; simp [logSemigroup]
    have hd : deriv (semigroup h f) = semigroup h (deriv f) := funext (fun z =>
      (hasDerivAt_semigroup (hf.smooth.of_le (by simp)) hLip h z).deriv)
    have hm : tiltedMean 0 h (fun _ => 0) (deriv f) = semigroup h (deriv f) := by
      funext z; simp [tiltedMean, semigroup]
    rw [he, iteratedDeriv_succ', hd]
    simpa only [hm] using hC h x
  · obtain ⟨C,hC⟩ := uniform_tiltedMean_bounds hf hLip hf.deriv_bounded hc n
    refine ⟨C, fun h x => ?_⟩
    have hd : deriv (logSemigroup c h f) = tiltedMean c h f (deriv f) := funext (fun z =>
      (hasDerivAt_logSemigroup (hf.smooth.of_le (by simp)) hLip (lt_of_le_of_ne hc (Ne.symm hc0)) h z).deriv)
    rw [iteratedDeriv_succ', hd]
    exact hC h x

lemma regularDatum_varianceLogHeat {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) {c : ℝ} (hc : 0 ≤ c) (t : ℝ) :
    RegularDatum (varianceLogHeat c t f) := by
  have he : varianceLogHeat c t f = logSemigroup c (Real.toNNReal t) f :=
    funext (varianceLogHeat_eq_logSemigroup_toNNReal hf.smooth.continuous.measurable c t)
  rw [he]
  exact regularDatum_logSemigroup hf hLip hc _

lemma uniform_varianceLogHeat_derivative_bounds {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    ∃ C : ℝ≥0, ∀ t x : ℝ, |iteratedDeriv (n+1) (varianceLogHeat c t f) x| ≤ C := by
  obtain ⟨C,hC⟩ := uniform_logSemigroup_derivative_bounds hf hLip hc n
  refine ⟨C, fun t x => ?_⟩
  have he : varianceLogHeat c t f = logSemigroup c (Real.toNNReal t) f :=
    funext (varianceLogHeat_eq_logSemigroup_toNNReal hf.smooth.continuous.measurable c t)
  rw [he]
  exact hC _ x

lemma varianceLogHeat_lipschitz {f : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    {c : ℝ} (hc : 0 ≤ c) (t : ℝ) : LipschitzWith K (varianceLogHeat c t f) := by
  have he : varianceLogHeat c t f = logSemigroup c (Real.toNNReal t) f :=
    funext (varianceLogHeat_eq_logSemigroup_toNNReal hf.continuous.measurable c t)
  rw [he]
  exact logSemigroup_lipschitz hf hc _

def varianceTilted (c t : ℝ) (f g : ℝ → ℝ) (x : ℝ) :=
  varianceHeat t (fun z => g z*Real.exp (c*f z)) x /
    varianceHeat t (fun z => Real.exp (c*f z)) x

lemma varianceTilted_eq_tiltedMean {f g : ℝ → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (c t x : ℝ) : varianceTilted c t f g x = tiltedMean c (Real.toNNReal t) f g x := by
  unfold varianceTilted tiltedMean
  have hwm : Measurable (fun z => g z*Real.exp (c*f z)) := hgm.mul ((measurable_const.mul hfm).exp)
  have hem : Measurable (fun z => Real.exp (c*f z)) := (measurable_const.mul hfm).exp
  rw [varianceHeat_eq_semigroup_toNNReal hwm t x, varianceHeat_eq_semigroup_toNNReal hem t x]

lemma varianceTilted_bound {f g : ℝ → ℝ} {K G : ℝ≥0} (hf : LipschitzWith K f)
    (hgm : Measurable g) (hG : ∀ z, |g z| ≤ G) (c t x : ℝ) :
    |varianceTilted c t f g x| ≤ G := by
  rw [varianceTilted_eq_tiltedMean hf.continuous.measurable hgm]
  exact tiltedMean_bound hf hgm hG c _ x

lemma weightExp_iteratedDeriv_weight {f g : ℝ → ℝ} (hf : RegularDatum f)
    (hg : BoundedSmooth g) (c : ℝ) (n : ℕ) :
    ∃ q : ℝ → ℝ, BoundedSmooth q ∧
      iteratedDeriv n (fun z => g z*Real.exp (c*f z)) = fun z => q z*Real.exp (c*f z) := by
  induction n with
  | zero => exact ⟨g, hg, by funext z; simp⟩
  | succ n IH =>
    obtain ⟨q,hq,he⟩ := IH
    exact ⟨fun z => deriv q z+c*q z*deriv f z, weighted_derivative_boundedSmooth hf hq c,
      by rw [iteratedDeriv_succ, he, deriv_weightExp hf hq c]⟩

lemma exponentialBound_weightExp_iteratedDeriv {f g : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (hg : BoundedSmooth g) (c : ℝ) (n : ℕ) :
    ExponentialBound (iteratedDeriv n (fun z => g z*Real.exp (c*f z))) := by
  obtain ⟨q,hq,he⟩ := weightExp_iteratedDeriv_weight hf hg c n
  obtain ⟨G,hG⟩ := hq.bound
  rw [he]
  exact (exponentialBound_exp hLip c).bdd_mul hG

end ZeroTemperatureSK.Heat

end
end
end
end

end OAI
