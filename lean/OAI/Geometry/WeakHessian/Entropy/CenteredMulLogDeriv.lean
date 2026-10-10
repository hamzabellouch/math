import Mathlib
import OAI.Geometry.WeakHessian.Entropy.FiniteEntropy

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
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory InformationTheory
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

lemma centered_mul_log_hasDeriv {B x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun r : ℝ => r*Real.log r-(Real.log B+1)*r)
      (Real.log x-Real.log B) x := by
  convert (Real.hasDerivAt_mul_log hx).sub ((hasDerivAt_id x).const_mul (Real.log B+1)) using 1 <;> first | rfl | ring

lemma centered_mul_log_antitone {B : ℝ} (hB : 0 < B) :
    AntitoneOn (fun r : ℝ => r*Real.log r-(Real.log B+1)*r) (Icc 0 B) := by
  apply antitoneOn_of_deriv_nonpos (f := fun r : ℝ => r*Real.log r-(Real.log B+1)*r) (convex_Icc _ _)
    ((Real.continuous_mul_log.sub (continuous_const.mul continuous_id)).continuousOn)
  · intro x hx
    rw [interior_Icc] at hx
    exact (centered_mul_log_hasDeriv hx.1.ne').differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    rw [(centered_mul_log_hasDeriv (B := B) hx.1.ne').deriv]
    exact sub_nonpos.mpr (Real.strictMonoOn_log.monotoneOn hx.1 hB hx.2.le)

lemma centered_mul_log_monotone {B : ℝ} (hB : 0 < B) :
    MonotoneOn (fun r : ℝ => r*Real.log r-(Real.log B+1)*r) (Ici B) := by
  apply monotoneOn_of_deriv_nonneg (f := fun r : ℝ => r*Real.log r-(Real.log B+1)*r) (convex_Ici _)
    ((Real.continuous_mul_log.sub (continuous_const.mul continuous_id)).continuousOn)
  · intro x hx
    rw [interior_Ici] at hx
    exact (centered_mul_log_hasDeriv (hB.trans hx).ne').differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    rw [(centered_mul_log_hasDeriv (B := B) (hB.trans hx).ne').deriv]
    exact sub_nonneg.mpr (Real.log_le_log hB hx.le)

lemma centered_mul_log_le_of_between {B r s : ℝ} (hB : 0 < B)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hrB : r ≤ B) (hmin : min s B ≤ r) :
    r*Real.log r-(Real.log B+1)*r ≤ s*Real.log s-(Real.log B+1)*s := by
  by_cases hsB : s ≤ B
  · rw [min_eq_left hsB] at hmin
    exact centered_mul_log_antitone hB ⟨hs,hsB⟩ ⟨hr,hrB⟩ hmin
  · have hBs := le_of_not_ge hsB
    rw [min_eq_right hBs] at hmin
    have he : r = B := le_antisymm hrB hmin
    rw [he]
    exact centered_mul_log_monotone hB (by change B ≤ B; exact le_refl B) (by simpa only [mem_Ici] using hBs) hBs

variable {X : Type*} [MeasurableSpace X]

lemma ae_le_of_withDensity_le {m : Measure X} [SigmaFinite m]
    {f g : X → ℝ≥0∞} (hf : AEMeasurable f m) (h : m.withDensity f ≤ m.withDensity g) :
    f ≤ᵐ[m] g := by
  apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite₀ hf
  intro A hA _
  simpa only [← withDensity_apply _ hA] using h A

lemma rnDeriv_le_of_domination {m μ : Measure X} [SigmaFinite m] [IsFiniteMeasure μ]
    {B : ℝ≥0∞} (h : μ ≤ B • m) (hac : μ ≪ m) : μ.rnDeriv m ≤ᵐ[m] fun _ => B := by
  apply ae_le_of_withDensity_le (Measure.measurable_rnDeriv _ _).aemeasurable
  rw [Measure.withDensity_rnDeriv_eq μ m hac,withDensity_const]
  exact h

lemma finiteEntropy_of_bounded_density {m μ : Measure X} [IsFiniteMeasure m] [IsFiniteMeasure μ]
    {B : ℝ≥0∞} (hBt : B ≠ ∞) (hd : μ ≤ B • m) : FiniteEntropy m μ := by
  have hac : μ ≪ m := (Measure.absolutelyContinuous_of_le hd).trans
    (Measure.AbsolutelyContinuous.rfl.smul_left B)
  refine ⟨hac,(integrable_rnDeriv_mul_log_iff hac).mp ?_⟩
  obtain ⟨M,hM⟩ := (isCompact_Icc (a := (0:ℝ)) (b := B.toReal)).exists_bound_of_continuousOn
    (f := fun r : ℝ => r*Real.log r) Real.continuous_mul_log.continuousOn
  apply (integrable_const M).mono'
    (Real.continuous_mul_log.measurable.comp (Measure.measurable_rnDeriv μ m).ennreal_toReal).aestronglyMeasurable
  filter_upwards [rnDeriv_le_of_domination hd hac] with x hx
  exact hM _ ⟨ENNReal.toReal_nonneg,ENNReal.toReal_mono hBt hx⟩

lemma entropyReal_le_of_density_capping {m : Measure X} [IsFiniteMeasure m]
    (μ η : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure η]
    (hE : FiniteEntropy m μ) {B : ℝ≥0∞} (hB : B ≠ 0) (hBt : B ≠ ∞)
    (hη : η ≤ B • m)
    (hlo : m.withDensity (fun x => min (μ.rnDeriv m x) B) ≤ η) :
    FiniteEntropy m η ∧ entropyReal m η ≤ entropyReal m μ := by
  have hEη := finiteEntropy_of_bounded_density hBt hη
  have hηr := rnDeriv_le_of_domination hη hEη.1
  have hl : (fun x => min (μ.rnDeriv m x) B) ≤ᵐ[m] η.rnDeriv m := by
    apply ae_le_of_withDensity_le ((Measure.measurable_rnDeriv _ _).min measurable_const).aemeasurable
    rwa [Measure.withDensity_rnDeriv_eq η m hEη.1]
  have hpoint : ∀ᵐ x ∂m,
      (η.rnDeriv m x).toReal*Real.log (η.rnDeriv m x).toReal -
        (Real.log B.toReal+1)*(η.rnDeriv m x).toReal ≤
      (μ.rnDeriv m x).toReal*Real.log (μ.rnDeriv m x).toReal -
        (Real.log B.toReal+1)*(μ.rnDeriv m x).toReal := by
    filter_upwards [hηr,hl,Measure.rnDeriv_lt_top μ m,Measure.rnDeriv_lt_top η m] with x hx hlx hμt hηt
    apply centered_mul_log_le_of_between (ENNReal.toReal_pos hB hBt)
      ENNReal.toReal_nonneg ENNReal.toReal_nonneg (ENNReal.toReal_mono hBt hx)
    rw [← ENNReal.toReal_min hμt.ne hBt]
    exact ENNReal.toReal_mono hηt.ne hlx
  have hIμ := (integrable_rnDeriv_mul_log_iff hE.1).mpr hE.2
  have hIη := (integrable_rnDeriv_mul_log_iff hEη.1).mpr hEη.2
  have hlinμ : Integrable (fun x => (Real.log B.toReal+1)*(μ.rnDeriv m x).toReal) m :=
    Measure.integrable_toReal_rnDeriv.const_mul _
  have hlinη : Integrable (fun x => (Real.log B.toReal+1)*(η.rnDeriv m x).toReal) m :=
    Measure.integrable_toReal_rnDeriv.const_mul _
  have H := integral_mono_ae (hIη.sub hlinη) (hIμ.sub hlinμ) hpoint
  simp only [Pi.sub_apply] at H
  rw [integral_sub hIη hlinη,integral_sub hIμ hlinμ,
    integral_const_mul,integral_const_mul,
    Measure.integral_toReal_rnDeriv hEη.1,Measure.integral_toReal_rnDeriv hE.1,
    probReal_univ,probReal_univ,mul_one] at H
  refine ⟨hEη,?_⟩
  rw [entropyReal_eq_integral_density hEη.1,entropyReal_eq_integral_density hE.1]
  linarith
end WeakHessian

end
end InlinedFile0

end OAI
