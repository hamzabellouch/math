import OAI.Analysis.LienardCycles.QuadraticCoordinates

namespace OAI

universe uP

open Set Filter MeasureTheory
open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.FixedWidthFamilies
open ScalarArcs ArcEndpoints ArcFamilies CanonicalVariation WidthCoordinates PartialCalculus ArchVariation

variable {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P]
variable (Φ : P × ℝ → ℝ) (hΦ : ContDiff ℝ ω Φ)
    (hloc : ∀ x : State P, ∃ f : State P × ℝ → State P,
      ContDiffAt ℝ ω f (x,0) ∧ ∀ᶠ q in 𝓝 (x,(0:ℝ)),
        f (q.1,0) = q.1 ∧ HasDerivAt (fun s => f (q.1,s)) (field Φ (f q)) q.2)
include hΦ hloc

lemma endpoint_formulas {p : P} {h r : ℝ} (hr : 0 < r) :
    lowerFamily Φ ((p,peakAtWidth Φ ((p,h),r)),h) =
      midpointAtWidth Φ ((p,h),r)+Φ (p,h)-r ∧
    upperFamily Φ ((p,peakAtWidth Φ ((p,h),r)),h) =
      midpointAtWidth Φ ((p,h),r)+Φ (p,h)+r := by
  have hs := (peak_spec Φ hΦ hloc (p := p) (h := h) hr).2
  dsimp [widthFamily,width] at hs
  dsimp [lowerFamily,upperFamily,midpointAtWidth,midpointFamily,ScalarArcs.midpoint]
  constructor <;> linarith

theorem witness {γ : ℝ → P} {θ h r : ℝ} (hγ : ContDiffAt ℝ ω γ θ) (hr : 0 < r) :
    ∃ u : ℝ × ℝ → ℝ,
      (∀ s, Continuous (fun y => u (s,y))) ∧
      (∀ y ∈ Icc (midpointAtWidth Φ ((γ θ,h),r)+Φ (γ θ,h)-r)
        (midpointAtWidth Φ ((γ θ,h),r)+Φ (γ θ,h)+r), ContDiffAt ℝ ω u (θ,y)) ∧
      (∀ y ∈ Icc (midpointAtWidth Φ ((γ θ,h),r)+Φ (γ θ,h)-r)
        (midpointAtWidth Φ ((γ θ,h),r)+Φ (γ θ,h)+r),
        ∀ᶠ q in 𝓝 (θ,y), HasDerivAt (fun s => u (q.1,s)) (Φ (γ q.1,u q)-q.2) q.2) ∧
      ∀ᶠ s in 𝓝 θ, IsArch (fun x => Φ (γ s,x)) (fun y => u (s,y)) h
        (peakAtWidth Φ ((γ s,h),r))
        (midpointAtWidth Φ ((γ s,h),r)+Φ (γ s,h)-r)
        (midpointAtWidth Φ ((γ s,h),r)+Φ (γ s,h)+r) := by
  let T : ℝ → ℝ := fun s => peakAtWidth Φ ((γ s,h),r)
  have hmap : ContDiffAt ℝ ω (fun s => ((γ s,h),r)) θ :=
    (hγ.prodMk contDiffAt_const).prodMk contDiffAt_const
  have hT : ContDiffAt ℝ ω T θ := by
    have hh := (peak_analytic Φ hΦ hloc (p := γ θ) (h := h) hr).comp θ hmap
    exact hh
  have hs := peak_spec Φ hΦ hloc (p := γ θ) (h := h) hr
  obtain ⟨w,hwc,_,hwd,hwe,hwa⟩ := endpoint_witness Φ hΦ hloc hs.1
  let u : ℝ × ℝ → ℝ := fun q => w ((γ q.1,T q.1),q.2)
  have hlift (y : ℝ) : ContDiffAt ℝ ω (fun q : ℝ × ℝ => ((γ q.1,T q.1),q.2)) (θ,y) :=
    ((hγ.comp (θ,y) contDiffAt_fst).prodMk (hT.comp (θ,y) contDiffAt_fst)).prodMk contDiffAt_snd
  have hf := endpoint_formulas Φ hΦ hloc (p := γ θ) (h := h) hr
  rw [hf.1,hf.2] at hwd hwe
  refine ⟨u,fun s => hwc (γ s,T s),fun y hy => (hwd y hy).comp (θ,y) (hlift y),?_,?_⟩
  · intro y hy
    filter_upwards [(hlift y).continuousAt.eventually (hwe y hy)] with q hq
    exact hq
  · have hc : ContinuousAt (fun s => ((γ s,T s),h)) θ :=
      (hγ.continuousAt.prodMk hT.continuousAt).prodMk continuousAt_const
    filter_upwards [hc.eventually hwa] with s hs
    have hh := endpoint_formulas Φ hΦ hloc (p := γ s) (h := h) hr
    simpa only [T,hh.1,hh.2] using hs

end QuinticLienard.FixedWidthFamilies

end OAI
