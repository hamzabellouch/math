import OAI.Analysis.LienardCycles.PositiveSymmetries

namespace OAI

universe uP

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter Metric
open scoped Topology ENNReal
open scoped Topology
open Set Filter MeasureTheory
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.PositiveFixedWidth
open ScalarArcs ArcEndpoints ArcFamilies PositiveVariation PositiveWidth PartialCalculus ArchVariation

variable {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P]
variable (Φ : P × ℝ → ℝ) (hΦ : ∀ q, 0<q.2 → ContDiffAt ℝ ω Φ q)
    (hloc : ∀ x : State P, 0<x.2.1 → ∃ f : State P × ℝ → State P,
      ContDiffAt ℝ ω f (x,0) ∧ ∀ᶠ q in 𝓝 (x,(0:ℝ)),
        f (q.1,0) = q.1 ∧ HasDerivAt (fun s => f (q.1,s)) (field Φ (f q)) q.2)
include hΦ hloc

lemma endpoint_formulas {p : P} {h r : ℝ} (hhpos : 0<h) (hr : 0 < r) :
    lowerFamily Φ ((p,peakAtWidth Φ ((p,h),r)),h) =
      midpointAtWidth Φ ((p,h),r)+Φ (p,h)-r ∧
    upperFamily Φ ((p,peakAtWidth Φ ((p,h),r)),h) =
      midpointAtWidth Φ ((p,h),r)+Φ (p,h)+r := by
  have hs := (peak_spec Φ hΦ hloc (p := p) (h := h) hhpos hr).2
  dsimp [widthFamily,width] at hs
  dsimp [lowerFamily,upperFamily,midpointAtWidth,midpointFamily,ScalarArcs.midpoint]
  constructor <;> linarith

theorem witness {γ : ℝ → P} {θ h r : ℝ} (hγ : ContDiffAt ℝ ω γ θ) (hhpos : 0<h) (hr : 0 < r) :
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
    have hh := (peak_analytic Φ hΦ hloc (p := γ θ) (h := h) hhpos hr).comp θ hmap
    exact hh
  have hs := peak_spec Φ hΦ hloc (p := γ θ) (h := h) hhpos hr
  obtain ⟨w,hwc,_,hwd,hwe,hwa⟩ := endpoint_witness Φ hΦ hloc hhpos hs.1
  let u : ℝ × ℝ → ℝ := fun q => w ((γ q.1,T q.1),q.2)
  have hlift (y : ℝ) : ContDiffAt ℝ ω (fun q : ℝ × ℝ => ((γ q.1,T q.1),q.2)) (θ,y) :=
    ((hγ.comp (θ,y) contDiffAt_fst).prodMk (hT.comp (θ,y) contDiffAt_fst)).prodMk contDiffAt_snd
  have hf := endpoint_formulas Φ hΦ hloc (p := γ θ) (h := h) hhpos hr
  rw [hf.1,hf.2] at hwd hwe
  refine ⟨u,fun s => hwc (γ s,T s),fun y hy => (hwd y hy).comp (θ,y) (hlift y),?_,?_⟩
  · intro y hy
    filter_upwards [(hlift y).continuousAt.eventually (hwe y hy)] with q hq
    exact hq
  · have hc : ContinuousAt (fun s => ((γ s,T s),h)) θ :=
      (hγ.continuousAt.prodMk hT.continuousAt).prodMk continuousAt_const
    filter_upwards [hc.eventually hwa] with s hs
    have hh := endpoint_formulas Φ hΦ hloc (p := γ s) (h := h) hhpos hr
    simpa only [T,hh.1,hh.2] using hs

end QuinticLienard.PositiveFixedWidth

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.PositiveParameterVariation
open ScalarArcs PartialCalculus ArchVariation

theorem zero_profile_variation {Φ u : ℝ × ℝ → ℝ} {Y B : ℝ → ℝ} {θ r t δ h : ℝ}
    (hΦ : ∀ q, 0<q.2 → ContDiffAt ℝ ω Φ q) (hzero : ∀ x, Φ (θ,x) = 0)
    (hY : DifferentiableAt ℝ Y θ) (hY0 : Y θ = 0) (hh : 0<h) (hr : 0 < r)
    (ha : IsArch (fun x => Φ (θ,x)) (fun y => u (θ,y)) h t (-r) r)
    (hu : ∀ y ∈ Icc (-r) r, ContDiffAt ℝ ω u (θ,y))
    (he : ∀ y ∈ Icc (-r) r, ∀ᶠ q in 𝓝 (θ,y),
      HasDerivAt (fun s => u (q.1,s)) (Φ (q.1,u q)-q.2) q.2)
    (hl : ∀ᶠ s in 𝓝 θ, u (s,Y s-r) = h)
    (hb : ∀ᶠ s in 𝓝 θ, u (s,Y s+r) = h)
    (hB : ∀ y ∈ Icc (-r) r,
      HasDerivAt B (first Φ (θ,(h+(r^2-y^2)/2))) y)
    (hBv : B r-B (-r) = 2*r*δ) : deriv Y θ = δ := by
  have hll : -r ∈ Icc (-r) r := ⟨le_rfl,by linarith⟩
  have hbb : r ∈ Icc (-r) r := ⟨by linarith,le_rfl⟩
  have hu0 : EqOn (fun y => u (θ,y)) (fun y => (h+(r^2-y^2)/2)) (Icc (-r) r) := by
    refine eq_of_hasDerivAt_eq_on_Icc ha.continuous.continuousOn (by fun_prop)
      (d := fun y => -y) ?_ ?_ hll (by simpa using ha.lower)
    · intro y hy
      simpa only [hzero,zero_sub] using ha.equation y hy
    · intro y _
      convert (((hasDerivAt_const y (r^2)).sub ((hasDerivAt_id y).pow 2)).div_const 2).const_add h using 1 <;>
        (first | rfl | (dsimp; ring))
  have hz (y : ℝ) (hy : y ∈ Icc (-r) r) :
      HasDerivAt (fun s => first u (θ,s)) (first Φ (θ,(h+(r^2-y^2)/2))) y := by
    have hs : second Φ (θ,u (θ,y)) = 0 := by
      apply (second_hasDerivAt ((hΦ _ (lt_of_lt_of_le hh (ha.range_mem y hy).1)).differentiableAt (by simp))).unique
      simpa only [hzero] using hasDerivAt_const (u (θ,y)) (0:ℝ)
    have hh := scalar_ode_variation (hu y hy) ((hΦ _ (lt_of_lt_of_le hh (ha.range_mem y hy).1)).differentiableAt (by simp)) (he y hy)
    have hv : u (θ,y) = (h+(r^2-y^2)/2) := hu0 hy
    rw [hs,zero_mul,add_zero,hv] at hh
    exact hh
  have hzc : ContinuousOn (fun y => first u (θ,y)) (Icc (-r) r) := by
    intro y hy
    exact ((first_contDiffAt (hu y hy)).continuousAt.comp
      (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  have hBc : ContinuousOn B (Icc (-r) r) := fun y hy => (hB y hy).continuousAt.continuousWithinAt
  have hv := eq_of_hasDerivAt_eq_on_Icc hzc (hBc.add continuousOn_const) hz
    (fun y hy => (hB y hy).add_const (first u (θ,-r)-B (-r))) hll (by dsimp; ring)
  have hend := hv hbb
  dsimp at hend
  have hel := hit_variation (by simpa only [hY0,zero_sub] using
      (hu (-r) hll).differentiableAt (by simp))
    (hY.sub_const r) (hasDerivAt_const θ h) hl
  have heb := hit_variation (by simpa only [hY0,zero_add] using
      (hu r hbb).differentiableAt (by simp))
    (hY.add_const r) (hasDerivAt_const θ h) hb
  have hesl : second u (θ,-r) = r := by
    apply (second_hasDerivAt ((hu (-r) hll).differentiableAt (by simp))).unique
    simpa only [hzero,sub_neg_eq_add,zero_add] using ha.equation (-r) hll
  have hesb : second u (θ,r) = -r := by
    apply (second_hasDerivAt ((hu r hbb).differentiableAt (by simp))).unique
    simpa only [hzero,zero_sub] using ha.equation r hbb
  simp only [hY0,zero_sub,zero_add,(hY.hasDerivAt.sub_const r).deriv,
    (hY.hasDerivAt.add_const r).deriv,hesl,hesb] at hel heb
  nlinarith

end QuinticLienard.PositiveParameterVariation

end OAI
