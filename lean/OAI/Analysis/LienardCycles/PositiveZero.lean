import OAI.Analysis.LienardCycles.PositiveParabolic

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
namespace QuinticLienard.PositiveZero
open ScalarArcs ArcFamilies PositiveWidth PartialCalculus ArchSymmetries
variable {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
variable (Φ : P × ℝ → ℝ) (hΦ : ∀ q, 0<q.2 → ContDiffAt ℝ ω Φ q)
    (hloc : ∀ x : State P, 0<x.2.1 → ∃ f : State P × ℝ → State P,
      ContDiffAt ℝ ω f (x,0) ∧ ∀ᶠ q in 𝓝 (x,(0:ℝ)),
        f (q.1,0)=q.1 ∧ HasDerivAt (fun s => f (q.1,s)) (field Φ (f q)) q.2)
include hΦ hloc
lemma zero_midpoint {p : P} (hz : ∀ x, Φ (p,x)=0) {h r : ℝ} (hh : 0<h) (hr : 0<r) :
    midpointAtWidth Φ ((p,h),r)=0 := by
  have he : (fun x => Φ (p,x))=(fun _ => (0:ℝ)) := funext hz
  have ha := ArchSymmetries.IsArch.affine (QuadraticCoordinates.parabolic_arch hr) (ψ:=fun _ => (0:ℝ))
    (H:=h) (C:=0) (by norm_num : (0:ℝ)<1) (by intro x; ring)
  simp only [one_pow,one_mul,zero_add,mul_zero,add_zero] at ha
  have ht : h<h+r^2/2 := by nlinarith [sq_pos_of_pos hr]
  have hc := canonical_of_positive_arch ha contDiffOn_const hh ht
  have hw : widthFamily Φ ((p,h+r^2/2),h)=r := by
    dsimp [widthFamily,width]
    rw [he,hc.1,hc.2]
    ring
  have hp := peak_eq Φ hΦ hloc hr hh ht hw
  dsimp only [midpointAtWidth]
  rw [hp]
  dsimp [midpointFamily,ScalarArcs.midpoint]
  rw [he,hc.1,hc.2,hz]
  ring

lemma zero_direction {γ : ℝ → P} (hγ : ContDiff ℝ ω γ) {h r δ : ℝ}
    (hbase : ∀ p, Φ (p,h)=0) (hz : ∀ x, Φ (γ 0,x)=0) (hh : 0<h) (hr : 0<r)
    {B : ℝ → ℝ}
    (hB : ∀ y ∈ Icc (-r) r, HasDerivAt B
      (first (fun q : ℝ × ℝ => Φ (γ q.1,q.2)) (0,h+(r^2-y^2)/2)) y)
    (hBv : B r-B (-r)=2*r*δ) :
    deriv (fun s => midpointAtWidth Φ ((γ s,h),r)) 0=δ := by
  let Y : ℝ → ℝ := fun s => midpointAtWidth Φ ((γ s,h),r)
  let Ψ : ℝ × ℝ → ℝ := fun q => Φ (γ q.1,q.2)
  have hΨ : ∀ q, 0<q.2 → ContDiffAt ℝ ω Ψ q := by
    intro q hq

    exact (hΦ (γ q.1,q.2) hq).comp q
      ((hγ.contDiffAt.comp q contDiffAt_fst).prodMk contDiffAt_snd)
  have hY : DifferentiableAt ℝ Y 0 := by
    have hm := PositiveWidth.midpointAtWidth_analytic Φ hΦ hloc (p:=γ 0) hh hr
    exact (hm.comp (f:=fun s => ((γ s,h),r)) 0
      ((hγ.contDiffAt.prodMk contDiffAt_const).prodMk contDiffAt_const)).differentiableAt (by simp)
  have hY0 : Y 0=0 := zero_midpoint Φ hΦ hloc hz hh hr
  obtain ⟨u,_,hud,hue,hua⟩ := PositiveFixedWidth.witness Φ hΦ hloc (θ:=0) hγ.contDiffAt hh hr
  have huv : midpointAtWidth Φ ((γ 0,h),r)=0 := hY0
  have hu : IsArch (fun x => Ψ (0,x)) (fun y => u (0,y)) h
      (peakAtWidth Φ ((γ 0,h),r)) (-r) r := by
    simpa only [huv,hbase,add_zero,zero_sub,zero_add] using hua.self_of_nhds
  have hd : ∀ y ∈ Icc (-r) r, ContDiffAt ℝ ω u (0,y) := by
    simpa only [huv,hbase,add_zero,zero_sub,zero_add] using hud
  have he : ∀ y ∈ Icc (-r) r, ∀ᶠ q in 𝓝 (0,y),
      HasDerivAt (fun s => u (q.1,s)) (Ψ (q.1,u q)-q.2) q.2 := by
    simpa only [huv,hbase,add_zero,zero_sub,zero_add] using hue
  exact PositiveParameterVariation.zero_profile_variation hΨ hz hY hY0 hh hr hu hd he
    (by filter_upwards [hua] with s hs; simpa only [Y,hbase,add_zero] using hs.lower)
    (by filter_upwards [hua] with s hs; simpa only [Y,hbase,add_zero] using hs.upper) hB hBv
end QuinticLienard.PositiveZero

end OAI
