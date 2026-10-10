import Mathlib
import OAI.Analysis.Conductivity.Sobolev.SobolevSmoothTests
import OAI.Analysis.Conductivity.Sobolev.LpExtension

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

def ballWholePiJetCLM : JetSpace →L[ℝ] Lp JetFiber 2 (volume : Measure (Fin 3 → ℝ)) :=
  ((Lp.compMeasurePreservingₗᵢ ℝ
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toHomeomorph.toMeasurableEquiv)
    (PiLp.volume_preserving_toLp (Fin 3))).toContinuousLinearMap).comp
      (lpZeroExtensionCLM Metric.isOpen_ball.measurableSet)

def ballWholePiComponentCLM (i : Fin 4) : JetSpace →L[ℝ] Lp ℝ 2 (volume : Measure (Fin 3 → ℝ)) :=
  ((EuclideanSpace.proj i).compLpL 2 volume).comp ballWholePiJetCLM

lemma smoothJet_zero_of_notMem_support {f : R3 → ℝ} {x : R3} (hx : x∉tsupport f) :
    smoothJet f x=0 := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change f x=0
    exact image_eq_zero_of_notMem_tsupport hx
  · simp [smoothJet,gradient,fderiv_of_notMem_tsupport ℝ hx]

lemma ballWholePiJetCLM_smooth_ae (f : R3 → ℝ)
    (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) (hs : tsupport f⊆ball) :
    ballWholePiJetCLM (smoothH1 f hf).val=ᵐ[volume]
      (fun y => smoothJet f (WithLp.toLp 2 y)) := by
  have he := lpZeroExtensionCLM_ae_of_ae (D:=ball) Metric.isOpen_ball.measurableSet
    (smoothH1 f hf).val (smoothJet_memLp hf).coeFn_toLp
  have he' : lpZeroExtensionCLM (D:=ball) Metric.isOpen_ball.measurableSet (smoothH1 f hf).val=ᵐ[volume] smoothJet f := by
    filter_upwards [he] with x hx
    rw [hx]
    by_cases hb : x∈ball
    · exact indicator_of_mem hb _
    · rw [indicator_of_notMem hb]
      exact (smoothJet_zero_of_notMem_support (fun h => hb (hs h))).symm
  apply (Lp.coeFn_compMeasurePreserving _ (PiLp.volume_preserving_toLp (Fin 3))).trans
  exact (PiLp.volume_preserving_toLp (Fin 3)).quasiMeasurePreserving.ae_eq_comp he'

lemma ballWholePiComponentCLM_ae (i : Fin 4) (z : JetSpace) :
    ballWholePiComponentCLM i z=ᵐ[volume] (fun y => ballWholePiJetCLM z y i) := by
  simp only [ballWholePiComponentCLM,ContinuousLinearMap.comp_apply]
  have he := (EuclideanSpace.proj (𝕜:=ℝ) i).coeFn_compLpL (p:=2)
    (μ:=(volume : Measure (Fin 3 → ℝ))) (ballWholePiJetCLM z)
  simpa only [EuclideanSpace.proj,PiLp.proj_apply] using he

lemma ballWholePiComponentCLM_smooth_ae (f : R3 → ℝ)
    (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) (hs : tsupport f⊆ball) (i : Fin 4) :
    ballWholePiComponentCLM i (smoothH1 f hf).val=ᵐ[volume]
      (fun y => smoothJet f (WithLp.toLp 2 y) i) := by
  filter_upwards [ballWholePiComponentCLM_ae i (smoothH1 f hf).val,
    ballWholePiJetCLM_smooth_ae f hf hs] with y hx hy
  rw [hx,hy]

end ScalarConductivity

end

end OAI
