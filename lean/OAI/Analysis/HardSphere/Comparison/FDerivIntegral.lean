import Mathlib

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace CompactParameterIntegral

variable {E A B : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup A] [NormedSpace ℝ A] [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  {μ : Measure A} [IsFiniteMeasureOnCompacts μ]

lemma hasFDerivAt_integral {F : E × A → B}
    (hF : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) F) {K : Set A} (hK : IsCompact K) (y : E) :
    HasFDerivAt (fun z : E ↦ ∫ x in K, F (z,x) ∂μ)
      (∫ x in K, (fderiv ℝ F (y,x)).comp (ContinuousLinearMap.inl ℝ E A) ∂μ) y := by
  let D : E × A → E →L[ℝ] B := fun z ↦
    (fderiv ℝ F z).comp (ContinuousLinearMap.inl ℝ E A)
  have hD : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) D :=
    (hF.fderiv_right (by simp)).clm_comp contDiff_const
  obtain ⟨C,hC⟩ := ((isCompact_closedBall y 1).prod hK).exists_bound_of_continuousOn
    hD.continuous.continuousOn
  have : IsFiniteMeasure (μ.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun z x ↦ F (z,x)) (F' := fun z x ↦ D (z,x)) (μ := μ.restrict K)
    (bound := fun _ ↦ C) (s := Metric.closedBall y 1) (Metric.closedBall_mem_nhds _ (by norm_num))
    (Eventually.of_forall fun z ↦ (hF.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (ContinuousOn.integrableOn_compact hK (hF.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn)
    (hD.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    ?_ (integrable_const _) ?_
  · filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    intro z hz
    exact hC (z,x) ⟨hz,hx⟩
  · exact Eventually.of_forall fun x z _ ↦ by
      have hh0 : HasFDerivAt (fun v : E ↦ (v,x)) (ContinuousLinearMap.inl ℝ E A) z :=
        (hasFDerivAt_id (𝕜 := ℝ) z).prodMk (hasFDerivAt_const (𝕜 := ℝ) x z)
      exact ((hF.differentiable (by simp)) (z,x)).hasFDerivAt.comp z hh0

lemma contDiff_integral_nat (n : ℕ) {F : E × A → B}
    (hF : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) F) {K : Set A} (hK : IsCompact K) :
    ContDiff ℝ n (fun z : E ↦ ∫ x in K, F (z,x) ∂μ) := by
  induction n generalizing B with
  | zero =>
    exact contDiff_zero.mpr (show Differentiable ℝ (fun z : E ↦ ∫ x in K, F (z,x) ∂μ) from
      fun y ↦ (hasFDerivAt_integral hF hK y).differentiableAt).continuous
  | succ n ih =>
    rw [show ((n+1:ℕ):WithTop ℕ∞)=(n:WithTop ℕ∞)+1 by simp,contDiff_succ_iff_fderiv]
    refine ⟨fun y ↦ (hasFDerivAt_integral hF hK y).differentiableAt,by simp,?_⟩
    have hd : fderiv ℝ (fun z : E ↦ ∫ x in K, F (z,x) ∂μ)=
        fun z ↦ ∫ x in K, (fderiv ℝ F (z,x)).comp (ContinuousLinearMap.inl ℝ E A) ∂μ := by
      funext z
      exact (hasFDerivAt_integral hF hK z).fderiv
    rw [hd]
    exact ih ((hF.fderiv_right (by simp)).clm_comp contDiff_const)

lemma contDiff_integral {F : E × A → B}
    (hF : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) F) {K : Set A} (hK : IsCompact K) :
    ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (fun z : E ↦ ∫ x in K, F (z,x) ∂μ) :=
  contDiff_infty.mpr fun n ↦ contDiff_integral_nat n hF hK

end CompactParameterIntegral

end

end OAI
