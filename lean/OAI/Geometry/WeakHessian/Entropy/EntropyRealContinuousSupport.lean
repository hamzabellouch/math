import Mathlib
import OAI.Geometry.WeakHessian.Entropy.CenteredMulLogDeriv
import OAI.Geometry.WeakHessian.Measure.IntegrableExpBounded

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Filter
open Set Filter MeasureTheory InformationTheory
open Set Filter
open scoped Topology
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set Filter Topology

namespace WeakHessian
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BoundedContinuousFunction

universe u
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [SecondCountableTopology X]
variable {m μ : Measure X} [IsFiniteMeasure m] [IsFiniteMeasure μ]

lemma entropyReal_continuous_support {B : ℝ≥0∞} (hB : B ≠ ∞)
    (hd : μ ≤ B • m) {ε : ℝ} (hε : 0 < ε) : ∃ g : X →ᵇ ℝ,
      entropyReal m μ ≤ (∫ x, g x ∂μ) - (∫ x, Real.exp (g x) ∂m) + μ.real univ + ε := by
  have hμ := finiteEntropy_of_bounded_density hB hd
  let C := max 1 B.toReal
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let δ := ε/(4*(1+m.real univ))
  have hmnon : 0 ≤ m.real univ := ENNReal.toReal_nonneg
  have hδ : 0 < δ := div_pos hε (by positivity)
  let M := C+δ
  have hM : 0 < M := add_pos hC hδ
  let r := fun x => min (μ.rnDeriv m x).toReal C
  have hrnon (x : X) : 0 ≤ r x := le_min ENNReal.toReal_nonneg hC.le
  have hrC (x : X) : r x ≤ C := min_le_right _ _
  have hrEq : r =ᵐ[m] fun x => (μ.rnDeriv m x).toReal := by
    filter_upwards [rnDeriv_le_of_domination hd hμ.1] with x hx
    exact min_eq_left ((ENNReal.toReal_mono hB hx).trans (le_max_right _ _))
  let f := fun x => Real.log (max δ (r x))
  have hf : Measurable f := Real.measurable_log.comp
    (measurable_const.max ((Measure.measurable_rnDeriv μ m).ennreal_toReal.min measurable_const))
  have htpos (x : X) : 0 < max δ (r x) := lt_of_lt_of_le hδ (le_max_left _ _)
  have hflo (x : X) : Real.log δ ≤ f x :=
    Real.log_le_log hδ (le_max_left _ _)
  have hfM (x : X) : f x ≤ Real.log M :=
    Real.log_le_log (htpos x) (max_le (by dsimp [M]; linarith) (by dsimp [M]; linarith [hrC x]))
  let A := |Real.log δ|+|Real.log M|
  have hfA (x : X) : ‖f x‖ ≤ A := by
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    constructor
    · dsimp [A]
      have H := neg_abs_le (Real.log δ)
      linarith [hflo x,abs_nonneg (Real.log M)]
    · dsimp [A]
      have H := le_abs_self (Real.log M)
      linarith [hfM x,abs_nonneg (Real.log δ)]
  have hfμ : Integrable f μ := Integrable.of_bound hf.aestronglyMeasurable A (ae_of_all _ hfA)
  have hfm : Integrable f m := Integrable.of_bound hf.aestronglyMeasurable A (ae_of_all _ hfA)
  have he := integrable_exp_of_bounded hf hfM m
  have hrf : Integrable (fun x => (μ.rnDeriv m x).toReal*f x) m :=
    (integrable_toReal_rnDeriv_mul_iff hμ.1).mpr hfμ
  have hr : Integrable (fun x => (μ.rnDeriv m x).toReal) m := by
    simpa only [mul_one] using (integrable_toReal_rnDeriv_mul_iff hμ.1).mpr (integrable_const (1:ℝ))
  have hlog : Integrable (fun x => (μ.rnDeriv m x).toReal*Real.log (μ.rnDeriv m x).toReal) m :=
    (integrable_rnDeriv_mul_log_iff hμ.1).mpr hμ.2
  have hpoint : ∀ᵐ x ∂m, (μ.rnDeriv m x).toReal*Real.log (μ.rnDeriv m x).toReal ≤
      (μ.rnDeriv m x).toReal*f x-Real.exp (f x)+(μ.rnDeriv m x).toReal+δ := by
    filter_upwards [hrEq] with x hx
    have H := mul_log_floor_gap (r := (μ.rnDeriv m x).toReal) ENNReal.toReal_nonneg hδ
    have hfexp : Real.exp (f x) = max δ (μ.rnDeriv m x).toReal := by
      dsimp [f]
      rw [Real.exp_log (htpos x),hx]
    have hfeq : f x = Real.log (max δ (μ.rnDeriv m x).toReal) := by dsimp [f]; rw [hx]
    rw [hfexp,hfeq]
    linarith
  have H := integral_mono_ae hlog (((hrf.sub he).add hr).add (integrable_const δ)) hpoint
  simp only [Pi.add_apply,Pi.sub_apply] at H
  rw [integral_add (f := fun x => (μ.rnDeriv m x).toReal*f x-Real.exp (f x)+(μ.rnDeriv m x).toReal)
      ((hrf.sub he).add hr) (integrable_const δ),
    integral_add (f := fun x => (μ.rnDeriv m x).toReal*f x-Real.exp (f x)) (hrf.sub he) hr,
    integral_sub hrf he,integral_toReal_rnDeriv_mul (f := f) hμ.1,Measure.integral_toReal_rnDeriv hμ.1,
    ← entropyReal_eq_integral_density hμ.1,integral_const,smul_eq_mul] at H
  obtain ⟨g,hg⟩ := exists_continuous_fenchel_approx (m := m) (μ := μ) hf hfA hM hfM (half_pos hε)
  refine ⟨g,?_⟩
  have hδeq : δ*(4*(1+m.real univ)) = ε := div_mul_cancel₀ ε (by positivity)
  have hδerr : m.real univ*δ ≤ ε/4 := by nlinarith
  linarith

lemma entropyReal_le_iff_continuous_support {B : ℝ≥0∞} (hB : B ≠ ∞)
    (hd : μ ≤ B • m) {a : ℝ} :
    entropyReal m μ ≤ a ↔ ∀ g : X →ᵇ ℝ,
      (∫ x, g x ∂μ) - (∫ x, Real.exp (g x) ∂m) + μ.real univ ≤ a := by
  constructor
  · intro ha g
    exact (entropyReal_fenchel (finiteEntropy_of_bounded_density hB hd) g).trans ha
  · intro ha
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨g,hg⟩ := entropyReal_continuous_support hB hd hε
    exact hg.trans (by linarith [ha g])

end WeakHessian

end
end InlinedFile0

end OAI
