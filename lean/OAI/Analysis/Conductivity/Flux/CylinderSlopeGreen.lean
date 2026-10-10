import Mathlib
import OAI.Analysis.Conductivity.Flux.CylinderCompletedGreen
import OAI.Analysis.Conductivity.Fourier.CylinderPoissonTrace

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma complex_linear_axis_smooth (r : ℝ) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (fun t : ℝ => (r:ℂ)*(t:ℂ)) :=
  contDiff_const.mul Complex.ofRealCLM.contDiff

lemma complex_linear_axis_deriv (r : ℝ) :
    deriv (fun t : ℝ => (r:ℂ)*(t:ℂ))=(fun _ => (r:ℂ)) := by
  funext t
  exact ((hasDerivAt_id t).ofReal_comp.const_mul (r:ℂ)).deriv.trans (by simp)

def cylinderSlopeJet (r R : ℝ) : FiniteCylinderJets R :=
  smoothCylinderModeJet (complex_linear_axis_smooth r) R 0

lemma cylinderSlopeJet_derivative (r R : ℝ) :
    cylinderSlopeJet r R 1=cylinderMode (FiniteAxisMeasure R) 0
      (smoothFiniteAxisLp (continuous_const : Continuous (fun _ : ℝ => (r:ℂ))) R) := by
  change cylinderMode _ _ (smoothFiniteAxisLp (q:=deriv (fun t : ℝ => (r:ℂ)*(t:ℂ))) _ _) = _
  congr 1
  apply Lp.ext
  filter_upwards [smoothFiniteAxisLp_ae ((complex_linear_axis_smooth r).continuous_deriv (by simp)) R,
    smoothFiniteAxisLp_ae (continuous_const : Continuous (fun _ : ℝ => (r:ℂ))) R] with t ht hu
  rw [ht,hu,complex_linear_axis_deriv]

lemma cylinderSlopeJet_angular (r R : ℝ) : cylinderSlopeJet r R 2=0 ∧ cylinderSlopeJet r R 3=0 := by
  simp [cylinderSlopeJet,smoothCylinderModeJet]

lemma constant_derivative_inner {q : ℝ → ℂ} (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q)
    (r R : ℝ) (hR : 0≤R) :
    inner ℂ (smoothFiniteAxisLp (continuous_const : Continuous (fun _ : ℝ => (r:ℂ))) R)
      (smoothFiniteAxisLp (hq.continuous_deriv (by simp)) R)=(r:ℂ)*(q R-q 0) := by
  rw [L2.inner_def]
  have he : (∫ t,inner ℂ
        (smoothFiniteAxisLp (continuous_const : Continuous (fun _ : ℝ => (r:ℂ))) R t)
        (smoothFiniteAxisLp (hq.continuous_deriv (by simp)) R t)∂FiniteAxisMeasure R)=
      ∫ t in Ioc (0:ℝ) R,(r:ℂ)*deriv q t := by
    apply integral_congr_ae
    filter_upwards [smoothFiniteAxisLp_ae (continuous_const : Continuous (fun _ : ℝ => (r:ℂ))) R,
      smoothFiniteAxisLp_ae (hq.continuous_deriv (by simp)) R] with t ht hu
    rw [ht,hu]
    simp only [RCLike.inner_apply,Complex.conj_ofReal,mul_comm]
  rw [he,integral_const_mul,←intervalIntegral.integral_of_le hR]
  rw [intervalIntegral.integral_deriv_eq_sub
    (fun t _ => hq.differentiable (by simp) t)
    ((hq.continuous_deriv (by simp)).intervalIntegrable 0 R)]

def spectralMeanCLM (s : Fin 3 → ℝ) : spectralTraceGraph (torusRate s) →L[ℂ] ℂ :=
  (lp.evalCLM ℂ (fun _ : TorusModes => ℂ) 2 0).comp
    ((PiLp.proj 2 (fun _ : Fin 2 => SpectralL2 TorusModes) 0).comp
      (spectralTraceGraph (torusRate s)).subtypeL)

lemma spectralMean_single (s : Fin 3 → ℝ) (h : TorusModes) (a : ℂ) :
    spectralMeanCLM s (spectralTraceSingleL s h a)=if h=0 then a else 0 := by
  change (lp.single 2 h a : SpectralL2 TorusModes) 0=_
  by_cases hh : h=0
  · subst h; simp
  · simp [lp.single_apply,hh]

lemma flatCylinder_slope_mode_green (s : Fin 3 → ℝ)
    {q : ℝ → ℂ} (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q) (r R : ℝ) (hR : 0≤R) (h : TorusModes) :
    flatCylinderEnergy s (cylinderSlopeJet r R) (smoothCylinderModeJet hq R h)=
      (r:ℂ)*(spectralMeanCLM s (spectralTraceSingleL s h (q R))-
        spectralMeanCLM s (spectralTraceSingleL s h (q 0))) := by
  rw [flatCylinderEnergy,cylinderSlopeJet_derivative,
    (cylinderSlopeJet_angular r R).1,(cylinderSlopeJet_angular r R).2]
  simp only [inner_zero_left,mul_zero,add_zero]
  change inner ℂ (cylinderMode _ 0 (smoothFiniteAxisLp continuous_const R))
    (cylinderMode _ h (smoothFiniteAxisLp (hq.continuous_deriv (by simp)) R))=_
  rw [cylinderMode_inner,spectralMean_single,spectralMean_single]
  by_cases hh : h=0
  · subst h
    rw [ite_eq_left rfl,ite_eq_left rfl]
    exact constant_derivative_inner hq r R hR
  · simp [hh,Ne.symm hh]

lemma spectralMean_polynomial (s : Fin 3 → ℝ) (t : ℝ) (p : TorusModes →₀ smoothComplexAxis) :
    spectralMeanCLM s (cylinderPolynomialTraceL s t p)=
      ∑ h∈p.support,spectralMeanCLM s (spectralTraceSingleL s h (p h t)) := by
  rw [cylinderPolynomialTraceL,Finsupp.lsum_apply,Finsupp.sum,map_sum]
  rfl

theorem flatCylinder_slope_completed_green (s : Fin 3 → ℝ) (r R : ℝ) (hR : 0≤R)
    (z : cylinderSobolevGraph s R) :
    flatCylinderEnergy s (cylinderSlopeJet r R) z.val.1=
      (r:ℂ)*(spectralMeanCLM s z.val.2.2-spectralMeanCLM s z.val.2.1) := by
  let J : CylinderTraceAmbient s R →L[ℂ] FiniteCylinderJets R := ContinuousLinearMap.fst ℂ _ _
  let T₀ : CylinderTraceAmbient s R →L[ℂ] spectralTraceGraph (torusRate s) :=
    (ContinuousLinearMap.fst ℂ _ _).comp (ContinuousLinearMap.snd ℂ _ _)
  let T₁ : CylinderTraceAmbient s R →L[ℂ] spectralTraceGraph (torusRate s) :=
    (ContinuousLinearMap.snd ℂ _ _).comp (ContinuousLinearMap.snd ℂ _ _)
  let L := (flatCylinderEnergyRightCLM s (cylinderSlopeJet r R)).comp J-
    (r:ℂ) • ((spectralMeanCLM s).comp T₁-(spectralMeanCLM s).comp T₀)
  have hr : LinearMap.range (cylinderPolynomialGraphL s R)≤L.ker := by
    rintro _ ⟨p,rfl⟩
    change flatCylinderEnergy s (cylinderSlopeJet r R) (cylinderPolynomialJetL R p)-
      (r:ℂ)*(spectralMeanCLM s (cylinderPolynomialTraceL s R p)-
        spectralMeanCLM s (cylinderPolynomialTraceL s 0 p))=0
    rw [cylinderPolynomialJetL_apply]
    change flatCylinderEnergyRightCLM s (cylinderSlopeJet r R) _-_ = 0
    rw [map_sum,spectralMean_polynomial,spectralMean_polynomial]
    change (∑ h∈p.support,flatCylinderEnergy s (cylinderSlopeJet r R)
      (smoothCylinderModeJet (smoothComplexAxis_smooth (p h)) R h))-_ = 0
    simp only [flatCylinder_slope_mode_green s _ r R hR,
      Finset.mul_sum,Finset.sum_sub_distrib,mul_sub]
    ring
  exact sub_eq_zero.mp (Submodule.topologicalClosure_minimal _ hr L.isClosed_ker z.property)

end ScalarConductivity



namespace ScalarConductivity
open Set MeasureTheory Filter Topology

def cylinderEndJet (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (r R : ℝ) (hR : 0≤R) (f : spectralTraceGraph (torusRate s)) : FiniteCylinderJets R :=
  endPoissonJet s hs R hR f+cylinderSlopeJet r R

lemma cylinderSlopeJet_mem_graph (s : Fin 3 → ℝ) (r R : ℝ) :
    (cylinderSlopeJet r R,(0,spectralTraceSingleL s 0 ((r:ℂ)*(R:ℂ))))∈cylinderSobolevGraph s R := by
  apply Submodule.le_topologicalClosure
  refine ⟨Finsupp.single 0 (⟨fun t : ℝ => (r:ℂ)*(t:ℂ),complex_linear_axis_smooth r⟩ : smoothComplexAxis),?_⟩
  apply Prod.ext
  · exact cylinderPolynomialJetL_single R 0 _
  · apply Prod.ext
    · change cylinderPolynomialTraceL s 0 _=_
      rw [cylinderPolynomialTraceL_single]
      simp only [Complex.ofReal_zero,mul_zero,map_zero]
    · change cylinderPolynomialTraceL s R _=_
      rw [cylinderPolynomialTraceL_single]

theorem cylinderEndJet_mem_graph (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (r R : ℝ) (hR : 0≤R) (f : spectralTraceGraph (torusRate s)) :
    (cylinderEndJet s hs r R hR f,
      (f,spectralPoissonTrace s R f+spectralTraceSingleL s 0 ((r:ℂ)*(R:ℂ))))∈
        cylinderSobolevGraph s R := by
  have H := (cylinderSobolevGraph s R).add_mem (endPoissonJet_mem_trace_graph s hs R hR f)
    (cylinderSlopeJet_mem_graph s r R)
  simpa only [Prod.mk_add_mk,add_zero,cylinderEndJet] using H

lemma spectralWeightedPair_real (s : Fin 3 → ℝ) (f g : spectralTraceGraph (torusRate s)) :
    (spectralWeightedPairL s (f.val 1) g).re=
      inner ℝ (spectralGraphWeight (torusRate s) f) (spectralGraphWeight (torusRate s) g) := by
  change (inner ℂ (f.val 1) (g.val 1)).re=inner ℝ (f.val 1) (g.val 1)
  rw [lp.inner_eq_tsum (𝕜:=ℂ),Complex.re_tsum (lp.summable_inner (𝕜:=ℂ) (f.val 1) (g.val 1)),
    lp.inner_eq_tsum (𝕜:=ℝ)]
  rfl

lemma spectralMean_real (s : Fin 3 → ℝ) (g : spectralTraceGraph (torusRate s)) :
    (spectralMeanCLM s g).re=spectralGraphMean (torusRate s) g := rfl

def cylinderTerminalFlux (s : Fin 3 → ℝ) (r R : ℝ)
    (f g : spectralTraceGraph (torusRate s)) : ℝ :=
  r*spectralGraphMean (torusRate s) g-(spectralWeightedPairL s (spectralEndWeight s R f) g).re

theorem cylinderEndJet_real_green (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (r : ℝ) {R : ℝ} (hR : 0<R) (f : spectralTraceGraph (torusRate s))
    (z : cylinderSobolevGraph s R) :
    (flatCylinderEnergy s (cylinderEndJet s hs r R hR.le f) z.val.1).re=
      inner ℝ (spectralGraphWeight (torusRate s) f)
        (spectralGraphWeight (torusRate s) z.val.2.1)-
      r*spectralGraphMean (torusRate s) z.val.2.1+
      cylinderTerminalFlux s r R f z.val.2.2 := by
  have hadd : flatCylinderEnergy s (cylinderEndJet s hs r R hR.le f) z.val.1=
      flatCylinderEnergy s (endPoissonJet s hs R hR.le f) z.val.1+
        flatCylinderEnergy s (cylinderSlopeJet r R) z.val.1 :=
    map_add (flatCylinderEnergyLeftCLM s z.val.1) _ _
  rw [hadd,flatCylinder_completed_green s hs hR f z,
    flatCylinder_slope_completed_green s r R hR.le z]
  simp only [Complex.add_re,Complex.sub_re,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero,spectralWeightedPair_real,spectralMean_real,cylinderTerminalFlux]
  ring

end ScalarConductivity

end

end OAI
