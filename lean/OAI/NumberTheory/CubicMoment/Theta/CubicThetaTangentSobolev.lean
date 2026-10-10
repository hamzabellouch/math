import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCutoffEnergy
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.H1

namespace OAI

/-! The local complex energy has genuine real and imaginary Sobolev
components in Euclidean Sobolev space. The change from
product coordinates to the Hilbert tangent space preserves volume. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

namespace LocalSobolev
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean

lemma tangentCoordinates_measurePreserving : MeasurePreserving cubicThetaTangentCoordinates
    (volume : Measure CubicThetaTangent) (volume : Measure (ℂ × ℝ)) := by
  exact WithLp.volume_preserving_ofLp ℂ ℝ

def tangentBorelVolume : @Measure CubicThetaTangent (borel CubicThetaTangent) := by
  let : MeasurableSpace CubicThetaTangent := borel CubicThetaTangent
  let : BorelSpace CubicThetaTangent := ⟨rfl⟩
  exact volume

instance tangentBorelVolume_finiteOnCompacts :
    let : MeasurableSpace CubicThetaTangent := borel CubicThetaTangent
    IsFiniteMeasureOnCompacts tangentBorelVolume := by
  let : MeasurableSpace CubicThetaTangent := borel CubicThetaTangent
  let : BorelSpace CubicThetaTangent := ⟨rfl⟩
  change IsFiniteMeasureOnCompacts (volume : Measure CubicThetaTangent)
  infer_instance

def realTest (f : ℂ × ℝ → ℂ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    C1c (E:=CubicThetaTangent) :=
  ⟨fun u => (f (cubicThetaTangentCoordinates u)).re,
    (Complex.reCLM.contDiff.comp (hf.comp cubicThetaTangentCoordinates.contDiff)),
    (hc.comp_homeomorph cubicThetaTangentCoordinates.toHomeomorph).comp_left (by simp)⟩

def imagTest (f : ℂ × ℝ → ℂ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    C1c (E:=CubicThetaTangent) :=
  ⟨fun u => (f (cubicThetaTangentCoordinates u)).im,
    (Complex.imCLM.contDiff.comp (hf.comp cubicThetaTangentCoordinates.contDiff)),
    (hc.comp_homeomorph cubicThetaTangentCoordinates.toHomeomorph).comp_left (by simp)⟩

def realH1 (f : ℂ × ℝ → ℂ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    h1 (E:=CubicThetaTangent) (μ:=tangentBorelVolume) :=
  ⟨graph (E:=CubicThetaTangent) (μ:=tangentBorelVolume) (realTest f hf hc),
    Submodule.le_topologicalClosure _ ⟨realTest f hf hc,rfl⟩⟩

def imagH1 (f : ℂ × ℝ → ℂ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    h1 (E:=CubicThetaTangent) (μ:=tangentBorelVolume) :=
  ⟨graph (E:=CubicThetaTangent) (μ:=tangentBorelVolume) (imagTest f hf hc),
    Submodule.le_topologicalClosure _ ⟨imagTest f hf hc,rfl⟩⟩

lemma realTest_fderiv (f : ℂ × ℝ → ℂ) (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) (u : CubicThetaTangent) :
    fderiv ℝ (realTest f hf hc) u=Complex.reCLM.comp
      ((fderiv ℝ f (cubicThetaTangentCoordinates u)).comp
        cubicThetaTangentCoordinates.toContinuousLinearMap) := by
  exact (Complex.reCLM.hasFDerivAt.comp u
    ((hf.differentiable one_ne_zero _).hasFDerivAt.comp u
      cubicThetaTangentCoordinates.hasFDerivAt)).fderiv

lemma imagTest_fderiv (f : ℂ × ℝ → ℂ) (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) (u : CubicThetaTangent) :
    fderiv ℝ (imagTest f hf hc) u=Complex.imCLM.comp
      ((fderiv ℝ f (cubicThetaTangentCoordinates u)).comp
        cubicThetaTangentCoordinates.toContinuousLinearMap) := by
  exact (Complex.imCLM.hasFDerivAt.comp u
    ((hf.differentiable one_ne_zero _).hasFDerivAt.comp u
      cubicThetaTangentCoordinates.hasFDerivAt)).fderiv

lemma gradient_norm_sq (f : ℂ × ℝ → ℂ) (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) (u : CubicThetaTangent) :
    ‖grad (realTest f hf hc) u‖^2+‖grad (imagTest f hf hc) u‖^2=
      cubicThetaFunctionEnergy f (cubicThetaTangentCoordinates u) := by
  simp only [grad,LinearIsometryEquiv.norm_map,realTest_fderiv,imagTest_fderiv]
  exact (cubicThetaTangentEnergy_basis cubicThetaTangentBasis _).symm

end LocalSobolev
end CubicFirstMoment

end

end OAI
