import Mathlib
import OAI.Analysis.Conductivity.Fourier.AnalyticDerivativeBounds
import OAI.Analysis.Conductivity.Variational.WeakHarmonicMean

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Laplacian InnerProductSpace

lemma WeaklyHarmonicOn.mono {f : WeylSpace → ℝ} {U V : Set WeylSpace}
    (hw : WeaklyHarmonicOn f U) (hV : V⊆U) : WeaklyHarmonicOn f V := by
  intro ψ hψ hc hs
  exact hw ψ hψ hc (hs.trans hV)

theorem smooth_weak_harmonic_analyticAt {f : WeylSpace → ℝ} {U : Set WeylSpace}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hw : WeaklyHarmonicOn f U)
    (hU : IsOpen U) {a : WeylSpace} (ha : a∈U) : AnalyticAt ℝ f a := by
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds ha)
  let b : ContDiffBump a := {
    rIn := r/2, rOut := r, rIn_pos := by positivity, rIn_lt_rOut := by linarith }
  let g : WeylSpace → ℝ := fun x => b x*f x
  have hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g := b.contDiff.mul hf
  have hc : HasCompactSupport g := b.hasCompactSupport.mul_right
  have he : EqOn f g (Metric.ball a (r/2)) := by
    intro x hx
    have hb : b x=1 := b.one_of_mem_closedBall (Metric.ball_subset_closedBall hx)
    simp [g,hb]
  have hwg : WeaklyHarmonicOn g (Metric.ball a (r/2)) :=
    .congr_restrict Metric.isOpen_ball.measurableSet
      ((ae_restrict_iff' Metric.isOpen_ball.measurableSet).mpr (ae_of_all _ he))
      (hw.mono ((Metric.ball_subset_ball (by linarith)).trans hsub))
  have hgA : AnalyticAt ℝ g a :=
    (weaklyHarmonic_smooth_mean hg hc hwg).analyticAt hg hc (by positivity)
  apply hgA.congr
  filter_upwards [Metric.ball_mem_nhds a (by positivity : 0<r/2)] with x hx
  exact (he hx).symm

theorem weakWeyl_analytic_local {f : WholeL2} {U : Set WeylSpace}
    (hw : WeaklyHarmonicOn f U) {a : WeylSpace} {R : ℝ} (hR : 0<R)
    (hball : Metric.closedBall a R⊆U) :
    AnalyticOnNhd ℝ (radialMollify f (R/4)) (Metric.ball a (R/4)) ∧
    (f : WeylSpace → ℝ) =ᵐ[volume.restrict (Metric.ball a (R/4))] radialMollify f (R/4) := by
  obtain ⟨hg,he⟩ := weakWeyl_local hw hR hball
  refine ⟨?_,he⟩
  have hb : Metric.ball a (R/4)⊆U :=
    ((Metric.ball_subset_ball (by linarith)).trans Metric.ball_subset_closedBall).trans hball
  have hwg := WeaklyHarmonicOn.congr_restrict Metric.isOpen_ball.measurableSet he (hw.mono hb)
  intro x hx
  exact smooth_weak_harmonic_analyticAt hg hwg Metric.isOpen_ball hx

end ScalarConductivity

end

end OAI
