import OAI.Analysis.LienardCycles.ZeroVariation

namespace OAI

open Set Filter MeasureTheory
open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter
open scoped Topology ContDiff

namespace QuinticLienard.QuadraticVariation
open ScalarArcs ArcFamilies PolynomialModel QuadraticCoordinates WidthCoordinates
  PartialCalculus ParameterVariation

lemma zero_direction {γ : ℝ → ℝ × ℝ} (hγ : ContDiff ℝ ω γ) {θ r δ : ℝ}
    (hγ0 : γ θ = (0,0)) (hr : 0 < r) {B : ℝ → ℝ}
    (hB : ∀ y ∈ Icc (-r) r, HasDerivAt B
      (first (fun q : ℝ × ℝ => profile (γ q.1,q.2)) (θ,(r^2-y^2)/2)) y)
    (hBv : B r-B (-r) = 2*r*δ) : deriv (fun s => H (γ s,r)) θ = δ := by
  let Y : ℝ → ℝ := fun s => H (γ s,r)
  let Φ : ℝ × ℝ → ℝ := fun q => profile (γ q.1,q.2)
  have hΦ : ContDiff ℝ ω Φ := profile_contDiff.comp
    ((hγ.comp contDiff_fst).prodMk contDiff_snd)
  have hz : Y θ = 0 := by simpa only [Y,hγ0] using (zero_data hr).2
  have hY : DifferentiableAt ℝ Y θ := by
    have hh := (H_analytic (d := (γ θ).1) (k := (γ θ).2) hr).comp θ
      (hγ.contDiffAt.prodMk contDiffAt_const)
    exact hh.differentiableAt (by simp)
  obtain ⟨u,huc,hud,hue,hua⟩ := FixedWidthFamilies.witness profile profile_contDiff model_local_flow
    (θ := θ) (h := 0) hγ.contDiffAt hr
  have huv : midpointAtWidth profile ((γ θ,0),r) = 0 := hz
  have hu : IsArch (fun x => Φ (θ,x)) (fun y => u (θ,y)) 0
      (peakAtWidth profile ((γ θ,0),r)) (-r) r := by
    simpa only [huv,profile_zero,add_zero,zero_sub,zero_add] using hua.self_of_nhds
  have hd : ∀ y ∈ Icc (-r) r, ContDiffAt ℝ ω u (θ,y) := by
    simpa only [huv,profile_zero,add_zero,zero_sub,zero_add] using hud
  have he : ∀ y ∈ Icc (-r) r, ∀ᶠ q in 𝓝 (θ,y),
      HasDerivAt (fun s => u (q.1,s)) (Φ (q.1,u q)-q.2) q.2 := by
    simpa only [huv,profile_zero,add_zero,zero_sub,zero_add] using hue
  apply zero_profile_variation hΦ (by intro x; simp [Φ,hγ0,profile]) hY hz hr hu hd he
    (by filter_upwards [hua] with s hs; simpa only [Y,H,profile_zero,add_zero] using hs.lower)
    (by filter_upwards [hua] with s hs; simpa only [Y,H,profile_zero,add_zero] using hs.upper) hB hBv

lemma P_zero {r : ℝ} (hr : 0 < r) : P ((0,0),r) = r^2/3 := by
  rw [←(P_hasDerivAt (d := 0) (k := 0) hr).deriv]
  apply zero_direction (contDiff_id.prodMk contDiff_const) (θ := 0) rfl hr
    (B := fun y => r^2*y/2-y^3/6)
  · intro y hy
    change HasDerivAt _ (first (fun q : ℝ × ℝ => profile ((q.1,0),q.2)) (0,_)) y
    rw [slope_first]
    convert (((hasDerivAt_id y).const_mul (r^2)).div_const 2).sub
      (((hasDerivAt_id y).pow 3).div_const 6) using 1 <;>
        (first | rfl | (dsimp; ring))
  · ring

lemma Q_zero {r : ℝ} (hr : 0 < r) : Q ((0,0),r) = r^4/15 := by
  rw [←(Q_hasDerivAt (d := 0) (k := 0) hr).deriv]
  apply zero_direction (contDiff_const.prodMk contDiff_id) (θ := 0) rfl hr
    (B := fun y => r^4*y/8-r^2*y^3/12+y^5/40)
  · intro y hy
    change HasDerivAt _ (first (fun q : ℝ × ℝ => profile ((0,q.1),q.2)) (0,_)) y
    rw [curvature_first]
    convert ((((hasDerivAt_id y).const_mul (r^4)).div_const 8).sub
      ((((hasDerivAt_id y).pow 3).const_mul (r^2)).div_const 12)).add
      (((hasDerivAt_id y).pow 5).div_const 40) using 1 <;>
        (first | rfl | (dsimp; ring))
  · ring

end QuinticLienard.QuadraticVariation

end OAI
