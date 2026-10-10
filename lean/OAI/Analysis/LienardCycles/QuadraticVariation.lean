import OAI.Analysis.LienardCycles.ParameterVariation

namespace OAI

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
namespace QuinticLienard.QuadraticVariation
open ScalarArcs ArcFamilies PolynomialModel QuadraticCoordinates WidthCoordinates
  PartialCalculus ParameterVariation

lemma profile_zero (p : ℝ × ℝ) : profile (p,0) = 0 := by simp [profile]

lemma direction_positive {γ : ℝ → ℝ × ℝ} (hγ : ContDiff ℝ ω γ) {θ r : ℝ}
    (hr : 0 < r)
    (hpos : ∀ x, 0 < x → 0 < first (fun q : ℝ × ℝ => profile (γ q.1,q.2)) (θ,x)) :
    0 < deriv (fun s => H (γ s,r)) θ := by
  let Y : ℝ → ℝ := fun s => H (γ s,r)
  let Φ : ℝ × ℝ → ℝ := fun q => profile (γ q.1,q.2)
  have hΦ : ContDiff ℝ ω Φ := profile_contDiff.comp
    ((hγ.comp contDiff_fst).prodMk contDiff_snd)
  have hY : DifferentiableAt ℝ Y θ := by
    have hh := (H_analytic (d := (γ θ).1) (k := (γ θ).2) hr).comp θ
      (hγ.contDiffAt.prodMk contDiffAt_const)
    exact hh.differentiableAt (by simp)
  obtain ⟨u,huc,hud,hue,hua⟩ := FixedWidthFamilies.witness profile profile_contDiff model_local_flow
    (h := 0) hγ.contDiffAt hr
  have hu : IsArch (fun x => Φ (θ,x)) (fun y => u (θ,y)) 0
      (peakAtWidth profile ((γ θ,0),r)) (Y θ-r) (Y θ+r) := by
    simpa only [Y,H,profile_zero,add_zero] using hua.self_of_nhds
  have hd : ∀ y ∈ Icc (Y θ-r) (Y θ+r), ContDiffAt ℝ ω u (θ,y) := by
    simpa only [Y,H,profile_zero,add_zero] using hud
  have he : ∀ y ∈ Icc (Y θ-r) (Y θ+r), ∀ᶠ q in 𝓝 (θ,y),
      HasDerivAt (fun s => u (q.1,s)) (Φ (q.1,u q)-q.2) q.2 := by
    simpa only [Y,H,profile_zero,add_zero] using hue
  have hl : ∀ᶠ s in 𝓝 θ, u (s,Y s-r) = 0 := by
    filter_upwards [hua] with s hs
    simpa only [Y,H,profile_zero,add_zero] using hs.lower
  have hb : ∀ᶠ s in 𝓝 θ, u (s,Y s+r) = 0 := by
    filter_upwards [hua] with s hs
    simpa only [Y,H,profile_zero,add_zero] using hs.upper
  exact midpoint_positive hΦ (fun s => profile_zero (γ s)) hY hr hu hd he hl hb hpos

lemma slope_first (d k x : ℝ) :
    first (fun q : ℝ × ℝ => profile ((q.1,k),q.2)) (d,x) = x := by
  have hd : DifferentiableAt ℝ (fun q : ℝ × ℝ => profile ((q.1,k),q.2)) (d,x) := by
    have hh : ContDiff ℝ ω (fun q : ℝ × ℝ => profile ((q.1,k),q.2)) :=
      profile_contDiff.comp ((contDiff_fst.prodMk contDiff_const).prodMk contDiff_snd)
    exact hh.differentiable (by simp) _
  apply (first_hasDerivAt hd).unique
  simpa [profile] using! ((hasDerivAt_id d).mul_const x).add_const (k/2*x^2)

lemma curvature_first (d k x : ℝ) :
    first (fun q : ℝ × ℝ => profile ((d,q.1),q.2)) (k,x) = x^2/2 := by
  have hd : DifferentiableAt ℝ (fun q : ℝ × ℝ => profile ((d,q.1),q.2)) (k,x) := by
    have hh : ContDiff ℝ ω (fun q : ℝ × ℝ => profile ((d,q.1),q.2)) :=
      profile_contDiff.comp ((contDiff_const.prodMk contDiff_fst).prodMk contDiff_snd)
    exact hh.differentiable (by simp) _
  apply (first_hasDerivAt hd).unique
  have hh : HasDerivAt (fun s => d*x+s/2*x^2) ((1/2)*x^2) k := by
    simpa using! (((hasDerivAt_id k).div_const 2).mul_const (x^2)).const_add (d*x)
  have he : (1/2:ℝ)*x^2 = x^2/2 := by ring
  rw [he] at hh
  simpa only [profile] using! hh

theorem P_pos {d k r : ℝ} (hr : 0 < r) : 0 < P ((d,k),r) := by
  rw [←(P_hasDerivAt (d := d) (k := k) hr).deriv]
  apply direction_positive (contDiff_id.prodMk contDiff_const) hr
  intro x hx
  change 0 < first (fun q : ℝ × ℝ => profile ((q.1,k),q.2)) (d,x)
  simpa only [slope_first] using hx

theorem Q_pos {d k r : ℝ} (hr : 0 < r) : 0 < Q ((d,k),r) := by
  rw [←(Q_hasDerivAt (d := d) (k := k) hr).deriv]
  apply direction_positive (contDiff_const.prodMk contDiff_id) hr
  intro x hx
  change 0 < first (fun q : ℝ × ℝ => profile ((d,q.1),q.2)) (k,x)
  rw [curvature_first]
  exact div_pos (sq_pos_of_pos hx) (by norm_num)

end QuinticLienard.QuadraticVariation

end OAI
