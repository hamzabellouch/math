import Mathlib
import OAI.Geometry.PrescribedPotential.PatchCutoffs
import OAI.Geometry.PrescribedPotential.RealSobolev
import OAI.Geometry.PrescribedPotential.GlobalHessian
import OAI.Geometry.PrescribedRicci.GlobalSmoothCompact
import OAI.Geometry.PrescribedRicci.PathUniformHigher

namespace OAI

/-! Smooth Path Limit. -/

section

 

noncomputable section
open Set Filter Topology Matrix
open scoped ContDiff Classical ComplexOrder
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)

lemma pointwise_of_sobolev (f : ℕ → Smooth A) (F : Smooth A)
    (hlim : ∀ k : ℕ, Tendsto (fun n => D.localizers.embed (k:ℝ) (f n)) atTop
      (𝓝 (D.localizers.embed (k:ℝ) F))) (x : X) :
    Tendsto (fun n => f n x) atTop (𝓝 (F x)) := by
  let k := Module.finrank ℝ (EC d)+1
  have hs : (Module.finrank ℝ (EC d):ℝ) < 2*(k:ℝ) := by
    exact_mod_cast (by dsimp [k]; omega : Module.finrank ℝ (EC d) < 2*k)
  have hl := ((D.localizers.strong (k:ℝ)).continuous.tendsto _).comp (hlim k)
  simp only [Function.comp_def,D.localizers.strong_embed _ hs] at hl
  exact ((BoundedContinuousFunction.lipschitz_eval_const x).continuous.tendsto _).comp hl

lemma real_of_sobolev (f : ℕ → SmoothRealFunction A) (F : Smooth A)
    (hlim : ∀ k : ℕ, Tendsto (fun n => D.localizers.embed (k:ℝ) (Smooth.ofReal (f n))) atTop
      (𝓝 (D.localizers.embed (k:ℝ) F))) : ∀ x, (F x).im = 0 := by
  intro x
  have h := Complex.continuous_im.continuousAt.tendsto.comp (D.pointwise_of_sobolev _ F hlim x)
  have hz : Tendsto (fun n => (Smooth.ofReal (f n) x).im) atTop (𝓝 (0:ℝ)) := tendsto_const_nhds
  exact tendsto_nhds_unique h hz

lemma hessian_of_sobolev (f : ℕ → SmoothRealFunction A) (φ : SmoothRealFunction A)
    (hlim : ∀ k : ℕ, Tendsto (fun n => D.localizers.embed (k:ℝ) (Smooth.ofReal (f n))) atTop
      (𝓝 (D.localizers.embed (k:ℝ) (Smooth.ofReal φ))))
    (p : ι) {x : X} (hx : x ∈ tsupport (D.localizers.weight p : X → ℂ)) (i j : Fin d) :
    Tendsto (fun n => (f n).hessian (D.patch p).index (A.chart (D.patch p).index x) i j)
      atTop (𝓝 (φ.hessian (D.patch p).index (A.chart (D.patch p).index x) i j)) := by
  have hl (k : ℕ) := ((D.completedHessian k p i j).continuous.tendsto _).comp (show
      Tendsto (fun n => D.localizers.embed ((k:ℝ)+2) (Smooth.ofReal (f n))) atTop
        (𝓝 (D.localizers.embed ((k:ℝ)+2) (Smooth.ofReal φ))) from by
          have h := hlim (k+2)
          rw [Nat.cast_add,Nat.cast_ofNat] at h
          exact h)
  have hh (k : ℕ) : Tendsto (fun n => D.localizers.embed (k:ℝ)
      (D.localizedHessian p i j (Smooth.ofReal (f n)))) atTop
      (𝓝 (D.localizers.embed (k:ℝ) (D.localizedHessian p i j (Smooth.ofReal φ)))) := by
    simpa only [Function.comp_def,D.completedHessian_embed] using hl k
  have h := D.pointwise_of_sobolev _ _ hh x
  simpa only [D.localizedHessian_source p i j _ hx] using h

variable [ConnectedSpace X]
theorem path_smooth_subsequence (line : SemipositiveAnticanonicalMetric A) (hd : 2 ≤ d)
    (z : ℕ → g.NormalizedPathSolution line) :
    ∃ φ : SmoothRealFunction A, ∃ ν : ℕ → ℕ, StrictMono ν ∧ ∀ k : ℕ,
      Tendsto (fun n => D.localizers.embed (k:ℝ) (Smooth.ofReal (z (ν n)).potential)) atTop
        (𝓝 (D.localizers.embed (k:ℝ) (Smooth.ofReal φ))) := by
  obtain ⟨F,ν,hν,hF⟩ := D.smooth_subsequence (fun n => Smooth.ofReal (z n).potential)
    (fun k => by
      obtain ⟨C,hC,hc⟩ := D.volumePath_uniform_all line hd k
      exact ⟨C,hC,fun n => hc (z n)⟩)
  let R : RealSmooth A := ⟨F,D.real_of_sobolev (fun n => (z (ν n)).potential) F hF⟩
  refine ⟨R.source,ν,hν,?_⟩
  rw [R.ofReal_source]
  exact hF
end GluingData
end GlobalElliptic

end
end

end OAI
