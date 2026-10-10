import Mathlib
import OAI.Analysis.Conductivity.Model

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Metric

variable {E P G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [SecondCountableTopology P]
  [MeasurableSpace P] [BorelSpace P] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [CompleteSpace G] {μ : Measure P} [IsLocallyFiniteMeasure μ]

omit [NormedSpace ℝ P] [CompleteSpace G] in
lemma hasFDerivAt_compact_integral {F : E × P → G} {D : E × P → E →L[ℝ] G}
    (hF : Continuous F) (hD : Continuous D)
    (hderiv : ∀ x p, HasFDerivAt (fun y => F (y,p)) (D (x,p)) x)
    {K : Set P} (hK : IsCompact K) (x : E) :
    HasFDerivAt (fun y => ∫ p in K, F (y,p) ∂μ) (∫ p in K, D (x,p) ∂μ) x := by
  obtain ⟨C,hC⟩ := ((isCompact_closedBall x 1).prod hK).exists_bound_of_continuousOn
    hD.continuousOn
  have hFd (y : E) : Continuous (fun p => F (y,p)) :=
    hF.comp (continuous_const.prodMk continuous_id)
  have hDd (y : E) : Continuous (fun p => D (y,p)) :=
    hD.comp (continuous_const.prodMk continuous_id)
  have hi : Integrable (fun _ : P => C) (μ.restrict K) :=
    ContinuousOn.integrableOn_compact hK continuous_const.continuousOn
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := μ.restrict K) (s := closedBall x 1) (bound := fun _ => C)
    (closedBall_mem_nhds x (by norm_num))
    (Filter.Eventually.of_forall fun y => (hFd y).aestronglyMeasurable)
    (ContinuousOn.integrableOn_compact hK (hFd x).continuousOn)
    (hDd x).aestronglyMeasurable _ hi
  · exact Filter.Eventually.of_forall (fun p y _ => hderiv y p)
  · filter_upwards [ae_restrict_mem hK.measurableSet] with p hp
    intro y hy
    exact hC (y,p) ⟨hy,hp⟩

lemma contDiff_compact_integral_nat (n : ℕ) {F : E × P → G}
    (hF : ContDiff ℝ n F) {K : Set P} (hK : IsCompact K) :
    ContDiff ℝ n (fun x => ∫ p in K, F (x,p) ∂μ) := by
  induction n generalizing G with
  | zero =>
    exact contDiff_zero.mpr (continuous_parametric_integral_of_continuous (f := fun x p => F (x,p)) hF.continuous hK)
  | succ n ih =>
    let D : E × P → E →L[ℝ] G := fun z =>
      (fderiv ℝ F z).comp (ContinuousLinearMap.inl ℝ E P)
    have hD : ContDiff ℝ n D := by
      exact (hF.fderiv_right (by norm_cast)).clm_comp contDiff_const
    have hderiv : ∀ x p, HasFDerivAt (fun y => F (y,p)) (D (x,p)) x := by
      intro x p
      have hf := (hF.differentiable (by norm_cast)).differentiableAt.hasFDerivAt
        (x := (x,p))
      exact hf.comp x ((hasFDerivAt_id x).prodMk (hasFDerivAt_const p x))
    rw [Nat.cast_add, Nat.cast_one]
    apply contDiff_succ_iff_hasFDerivAt.mpr
    exact ⟨fun x => ∫ p in K, D (x,p) ∂μ, ih hD,
      hasFDerivAt_compact_integral hF.continuous hD.continuous hderiv hK⟩

lemma contDiff_compact_integral {F : E × P → G}
    (hF : ContDiff ℝ (↑(⊤ : ℕ∞)) F) {K : Set P} (hK : IsCompact K) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => ∫ p in K, F (x,p) ∂μ) := by
  apply contDiff_infty.mpr
  intro n
  exact contDiff_compact_integral_nat n (contDiff_infty.mp hF n) hK

end ScalarConductivity

end

end OAI
