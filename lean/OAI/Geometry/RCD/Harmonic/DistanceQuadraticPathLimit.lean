import OAI.Geometry.RCD.Sobolev.PoissonPathDefectLimit
import OAI.Geometry.RCD.Sobolev.DistancePoissonAbsoluteValues
import OAI.Geometry.RCD.Harmonic.InteriorQuadraticComparison

namespace OAI

/-! # Absolute quadratic path errors for the actual distance functions -/

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X} {hn : 2≤n} [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]
  {κ B J C : ℝ} {p : ℕ → X} {r : ℕ → ℝ} {hr : ∀ k, 0<r k}
  {F : DistancePoissonFamily (hausdorff n X) hX.quadratic n κ B J C p r hr}
  (W : DistancePoissonMeanData F)
attribute [local instance] pathBorel pathBorelSpace

include hn W in
theorem DistancePoissonMeanData.normalized_distance_path_error (p₀ : X)
    (hK : K≤0) (hκ : 0≤κ) (hBJ : 0≤J+B/2) (hr1 : ∀ k, r k≤1)
    (hV : ∀ k, 0<(hausdorff n X).real (ball (p k) (r k)))
    (hr0 : Tendsto r atTop (𝓝 0)) {P Cπ : ℝ} (hP : 0≤P) (hCπ : 0≤Cπ)
    (hpoin : ∀ k, ∀ v : SobolevSpace.dirichlet (hausdorff n X) hX.quadratic (ball (p k) (r k)),
      ‖SobolevSpace.toLp (hausdorff n X) hX.quadratic v.val‖^2≤
        P*(r k)^2*energyForm (hausdorff n X) hX.quadratic v.val v.val)
    (hmass : Tendsto (fun k => (F.source k).real (ball (p k) (r k))/
      (hausdorff n X).real (ball (p k) (r k))) atTop (𝓝 0))
    (π : ℕ → Measure C(Time,X)) [∀ k, IsProbabilityMeasure (π k)]
    (hgeo : ∀ k, ∀ᵐ γ ∂π k, IsGeodesic γ)
    (hopt : ∀ k, IsOptimalCoupling ((π k).map (fun γ => γ 0)) ((π k).map (fun γ => γ 1))
      ((π k).map (fun γ => (γ 0,γ 1))))
    (Bπ : ℕ → ℝ≥0∞) (hBπ : ∀ k, Bπ k≠∞)
    (hcomp : ∀ k (t : Time), (π k).map (fun γ => γ t)≤Bπ k • hausdorff n X)
    (hs₀ : ∀ k, ∀ᵐ x ∂(π k).map (fun γ => γ 0), dist x (p k)≤r k/512)
    (hs₁ : ∀ k, ∀ᵐ x ∂(π k).map (fun γ => γ 1), dist x (p k)≤r k/512)
    (hcompression : ∀ k, (Bπ k).toReal*(hausdorff n X).real (ball (p k) (r k))≤Cπ)
    (l h t : Time) (hl : 0<(l:ℝ)) (hlh : (l:ℝ)<h) (hh : (h:ℝ)<1)
    (ht : (t:ℝ)∈Icc (l:ℝ) h) :
    Tendsto (fun k => (∫ γ, |interiorQuadraticDefect
      (fun x => dist (p k) x^2/2) l h t γ| ∂π k)/(r k)^2) atTop (𝓝 0) := by
  let q k x := dist (p k) x^2/2
  have hstay k (s : Time) : ∀ᵐ x ∂(π k).map (fun γ => γ s), x∈ball (p k) (r k/16) := by
    have hk := hr k
    have hb := optimal_geodesic_plan_bounded ((π k).map (fun γ => γ 0))
      ((π k).map (fun γ => γ 1)) (π k) (hgeo k) (hopt k) (p k)
      (by positivity : 0≤r k/512) (hs₀ k) (hs₁ k)
    apply (ae_map_iff (measurable_path_eval s).aemeasurable measurableSet_ball).mpr
    filter_upwards [hb] with γ hγ
    have hdist := hγ.2 s
    change dist (γ s) (p k)<r k/16
    linarith
  have hvalues (s : Time) : Tendsto (fun k =>
      (∫ γ, |q k (γ s)-W.representative k (γ s)| ∂π k)/(r k)^2) atTop (𝓝 0) := by
    have hv := W.normalized_distance_L1_error hP hCπ hV hpoin hmass
      (fun k => (π k).map (fun γ => γ s)) Bπ hBπ (fun k => hcomp k s)
      (fun k => hstay k s) hcompression
    convert hv using 1
    funext k
    obtain ⟨L,A,hL,_hc,_he,_hA⟩ := W.representative_spec k
    have hcont := hL.continuous
    rw [integral_map (measurable_path_eval s).aemeasurable (by fun_prop)]
  have hpoisson := W.normalized_path_error_tendsto_zero (hX := hX) (hn := hn) p₀
    hK hκ hBJ hr1 hV hr0 hmass π hgeo hopt Bπ hBπ hcomp hs₀ hs₁ hcompression l h t hl hlh hh ht
  have hsum := ((hpoisson.add (hvalues t)).add (hvalues l)).add (hvalues h)
  simp only [zero_add] at hsum
  apply squeeze_zero (fun k => div_nonneg (integral_nonneg fun _ => abs_nonneg _) (sq_nonneg _)) _ hsum
  intro k
  obtain ⟨L,A,hU,hUc,_hu,_hA⟩ := W.representative_spec k
  obtain ⟨M,hM⟩ := hUc.exists_bound_of_continuous hU.continuous
  have hui (s : Time) : Integrable (fun γ => W.representative k (γ s)) (π k) :=
    Integrable.of_bound (hU.continuous.measurable.comp (measurable_path_eval s)).aestronglyMeasurable M
      (Eventually.of_forall fun γ => hM (γ s))
  have hqi (s : Time) : Integrable (fun γ => q k (γ s)) (π k) := by
    have hqcont : Continuous (q k) := by dsimp only [q]; fun_prop
    apply Integrable.of_bound (hqcont.comp (continuous_eval_const s)).aestronglyMeasurable ((r k)^2/2)
    filter_upwards [ae_of_ae_map (measurable_path_eval s).aemeasurable (hstay k s)] with γ hγ
    have hdist : dist (p k) (γ s)<r k/16 := by simpa only [mem_ball,dist_comm] using hγ
    change |dist (p k) (γ s)^2/2|≤(r k)^2/2
    rw [abs_of_nonneg (by positivity)]
    nlinarith [dist_nonneg (x := p k) (y := γ s),hr k]
  have hfin := finite_second_moment_cost
    (finiteSecondMoment_of_bounded ((π k).map (fun γ => γ 0)) (p k) (hs₀ k))
    (finiteSecondMoment_of_bounded ((π k).map (fun γ => γ 1)) (p k) (hs₁ k)) (hopt k).1 (hopt k).2.1
  have hd := path_cost_integrable (π k) hfin
  have hip := interiorQuadraticDefect_integrable (π k) hU.continuous hUc hd l h t
  have hiq : Integrable (interiorQuadraticDefect (q k) l h t) (π k) :=
    ((hqi t).sub (hqi l) |>.sub (((hqi h).sub (hqi l)).div_const _ |>.mul_const _)).sub
      ((hd.mul_const _).mul_const _ |>.div_const _)
  have he (s : Time) := ((hqi s).sub (hui s)).abs
  have hbound := integral_mono_ae hiq.abs (((hip.abs.add (he t)).add (he l)).add (he h))
    (Eventually.of_forall fun γ => interiorQuadraticDefect_comparison (q k) (W.representative k) l h t hlh ht γ)
  have hadd : (∫ γ, |interiorQuadraticDefect (W.representative k) l h t γ|+
      |q k (γ t)-W.representative k (γ t)|+|q k (γ l)-W.representative k (γ l)|+
        |q k (γ h)-W.representative k (γ h)| ∂π k)=
      (∫ γ, |interiorQuadraticDefect (W.representative k) l h t γ| ∂π k)+
      (∫ γ, |q k (γ t)-W.representative k (γ t)| ∂π k)+
      (∫ γ, |q k (γ l)-W.representative k (γ l)| ∂π k)+
      (∫ γ, |q k (γ h)-W.representative k (γ h)| ∂π k) := by
    have h1 := integral_add ((hip.abs.add (he t)).add (he l)) (he h)
    have h2 := integral_add (hip.abs.add (he t)) (he l)
    have h3 := integral_add hip.abs (he t)
    simp only [Pi.add_apply,Pi.sub_apply] at h1 h2 h3
    rw [h1,h2,h3]
  simp only [Pi.add_apply,Pi.sub_apply] at hbound
  rw [hadd] at hbound
  rw [← add_div,← add_div,← add_div]
  exact div_le_div_of_nonneg_right hbound (sq_nonneg _)

end RegularPointCoordinates

end

end OAI
