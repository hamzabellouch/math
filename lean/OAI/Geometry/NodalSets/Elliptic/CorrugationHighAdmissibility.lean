import OAI.Geometry.NodalSets.Elliptic.CompactHessianUnitBound
import OAI.Geometry.NodalSets.Elliptic.CorrugationHighScalar
import OAI.Geometry.NodalSets.Elliptic.CorrugationRadialLoss
import OAI.Geometry.NodalSets.Elliptic.CorrugationUnitRegimeErrors
import OAI.Geometry.NodalSets.Spectral.CorrugationAngularProjection

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

theorem corrugation_actual_high_admissibility
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (S χ : Coord → ℝ)
    {D U : Set Coord} (hD : IsCompact D) (hconv : Convex ℝ D)
    (hU : IsOpen U) (hDU : D ⊆ U)
    (hg : ContDiffOn ℝ ∞ g U) (hS : ContDiffOn ℝ ∞ S U)
    (hp : ∀ y ∈ U, ∀ v, v ≠ 0 → 0 < g y v v)
    (hn : ∀ y ∈ D, metricGradient g S y ≠ 0)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1)
    {Aχ : ℝ} (hAχ : 0 < Aχ)
    (hχA : ∀ z, ‖fderiv ℝ χ z‖ ≤ Aχ*(χ z)^((7:ℝ)/8))
    {amp L : ℝ} (ha : 0 ≤ amp) (ha1 : amp ≤ 1) (hL : 0 < L)
    (hprod : ∀ r : ℝ, 0 ≤ r → corrugationSlope amp (1/4) r *
      max (-deriv (corrugationSlope amp (1/4)) r) 0 ≤ 1/(64*(1/4:ℝ))) :
    ∃ T : ℝ, 0 < T ∧ ∀ᶠ k : ℕ in atTop,
      ∀ y ∈ D, ∀ x ∈ D, ‖x-y‖ ≤ corrugationScale L k →
      ∀ e : Coord ≃L[ℝ] Coord,
      e (Pi.single 0 1) = (corrugationOldSlope g S y)⁻¹ • metricGradient g S y →
      (∀ i j, g y (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0) →
      let z := corrugationFastMap (corrugationFrequency k) (frozenFrameCovector e 2) (frozenFrameCovector e 3) (x-y)
      let t₀ := frozenPlaneVector e (-((corrugationCellPoint z).2/corrugationCellRadius z))
        ((corrugationCellPoint z).1/corrugationCellRadius z)
      let w := localizedCorrugation χ (corrugationPeriodicWell amp)
        (corrugationOldSlope g S y) (corrugationFrequency k) (corrugationScale L k)
        (frozenFrameCovector e 2) (frozenFrameCovector e 3) y
      let p := metricGradient g (S+w) x
      let e' := metricNormalize (g x) p
      let q := metricPerpProjection (g x) e' t₀
      let t := metricNormalize (g x) q
      T < corrugationFrequency k*χ ((corrugationScale L k)⁻¹ • (x-y))*
        corrugationSlope amp (1/4) (corrugationCellRadius z) →
      q ≠ 0 ∧ g x t t = 1 ∧ g x e' t = 0 ∧
        1 ≤ (g x p p/(g x p p+4))*sourceHessian g (S+w) x e' e'+sourceHessian g (S+w) x t t := by
  obtain ⟨H,hH,hHbound⟩ := compact_sourceHessian_unit_bound g S hD hU hDU hg hS hp
  obtain ⟨m,hm,B,hB,hslope⟩ := corrugationOldSlope_compact_bounds g S hD hU hDU hg hS hp hn
  obtain ⟨E,hE,herror⟩ := corrugation_actual_metric_unit_errors g χ hD hU hDU hg hp hχ hc
    (fun z ↦ ⟨hχ0 z,hχ1 z⟩) hAχ hχA ha ha1
  obtain ⟨D₀,hD₀,hloss⟩ := corrugation_actual_radial_loss
  obtain ⟨C,hC,hang⟩ := corrugation_actual_angular_estimates g S χ hD hconv hU hDU hg hS hp hn
    hχ hc hχ0 hχ1 ha ha1 hL
  have hnv := corrugation_local_nonvanishing g S χ hD hconv hU hDU hg hS hp hn hχ hc amp hL
  let T := (8*H+4)/m
  have hT : 0 < T := by dsimp [T]; positivity
  have hTm : m*T = 8*H+4 := by dsimp [T]; field_simp
  have hlim := corrugation_high_rates_tendsto hL.ne' hT
  have hlimR : Tendsto (fun k ↦ 3*C^2*D₀*corrugationHighRadialRate L T k) atTop (𝓝 0) :=
    by simpa using hlim.2.const_mul (3*C^2*D₀)
  have hlimE : Tendsto (fun k ↦ 2*E*corrugationHighErrorRate L T k) atTop (𝓝 0) :=
    by simpa using hlim.1.const_mul (2*E)
  refine ⟨T,hT,?_⟩
  filter_upwards [hang,hnv,hlimR.eventually_lt_const (by norm_num : (0:ℝ) < 1/8),
    hlimE.eventually_lt_const (by norm_num : (0:ℝ) < 1/4)] with k hka hknv hkR hkE
  intro y hy x hx hxy e he0 he
  dsimp only
  intro hreg
  let s := corrugationOldSlope g S y
  let J := corrugationFrequency k
  let R := corrugationScale L k
  let a := frozenFrameCovector e 2
  let b := frozenFrameCovector e 3
  let z := corrugationFastMap J a b (x-y)
  let r := corrugationCellRadius z
  let l := corrugationSlope amp (1/4) r
  let χ₀ := χ (R⁻¹ • (x-y))
  let Q := J*χ₀*l
  let w := localizedCorrugation χ (corrugationPeriodicWell amp) s J R a b y
  let p := metricGradient g (S+w) x
  let e' := metricNormalize (g x) p
  let t₀ := frozenPlaneVector e (-((corrugationCellPoint z).2/r)) ((corrugationCellPoint z).1/r)
  let q := metricPerpProjection (g x) e' t₀
  let t := metricNormalize (g x) q
  let ν := g x p p/(g x p p+4)
  let d := max (-deriv (corrugationSlope amp (1/4)) r) 0
  let rad := fun v ↦ radialComponent (corrugationCellPoint z) (a.prod b v) r
  let ang := fun v ↦ angularComponent (corrugationCellPoint z) (a.prod b v) r
  let F := fun v ↦ s*J*χ₀*fderiv ℝ (fderiv ℝ (corrugationPeriodicWell amp)) z (a.prod b v) (a.prod b v)
  let Err := fun v ↦ corrugationMetricError g χ (corrugationPeriodicWell amp) s J R a b y x v v
  let BE := E*s*corrugationHighErrorRate L T k*Q
  have hs : 0 < s := corrugationOldSlope_positive g S y (hp y (hDU hy)) (hn y hy)
  have hms : m ≤ s := (hslope y hy).1
  have hJ : 0 < J := corrugationFrequency_positive k
  have hR : 0 < R := corrugationScale_positive hL k
  have hχ₀ : 0 ≤ χ₀ := hχ0 _
  have hl : 0 ≤ l := corrugationSlope_nonneg ha (corrugationCellRadius_properties z).1
  have hl1 : l ≤ 1 := corrugationSlope_le_one ha ha1 (by norm_num) (by norm_num) (corrugationCellRadius_properties z).1
  obtain ⟨hχp,hlp,_,_⟩ := corrugation_high_regime_lower hχ₀ (hχ1 _) hl hl1 hJ hT hreg
  have hQ : 0 < Q := hT.trans hreg
  have hr0 : r ≠ 0 := by
    intro hr
    have hh : l = 0 := by dsimp [l]; rw [hr,corrugationSlope_center]
    linarith
  have hrpos : 0 < r := lt_of_le_of_ne (corrugationCellRadius_properties z).1 (Ne.symm hr0)
  have hr1 : r ≤ 1/4 := by
    by_contra hh
    have hz : l = 0 := corrugationSlope_zero (by norm_num) (le_of_lt (lt_of_not_ge hh))
    linarith
  obtain ⟨hnq,htu,hto,hat,hrt,hre⟩ := hka y hy x hx hxy e he0 he hr0
  have hp0 : 0 < g x p p := hp x (hDU hx) p (hknv y hy x hx hxy e he0 he)
  have heu : g x e' e' = 1 := metricNormalize_unit (g x) p hp0
  have hν0 : 0 ≤ ν := div_nonneg hp0.le (by positivity)
  have hν1 : ν ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  have hd : 0 ≤ d := le_max_right _ _
  have hdp : -d ≤ deriv (corrugationSlope amp (1/4)) r := by
    have hh := le_max_left (-deriv (corrugationSlope amp (1/4)) r) 0
    dsimp [d]; linarith
  have hrade : |rad e'| ≤ l+C*R := by
    rw [show rad e' = _ from frozen_radial_covector (g y) e he (corrugationCellPoint z) r e']
    exact hre.trans (add_le_add (mul_le_of_le_one_left hl (hχ1 _)) le_rfl)
  have hradt : |rad t| ≤ C*R := by
    rw [show rad t = _ from frozen_radial_covector (g y) e he (corrugationCellPoint z) r t]
    exact hrt
  have hangt : 1/2 ≤ ang t := by
    rw [show ang t = _ from frozen_angular_covector (g y) e he (corrugationCellPoint z) r t]
    exact hat
  have hradloss : R^2*d ≤ D₀*corrugationHighRadialRate L T k*l :=
    (hloss amp r χ₀ L T ha ha1 (corrugationCellRadius_properties z).1
      hχ₀ (hχ1 _) hL hT k).2 hreg
  have hradsmall : 3*d*(C*R)^2 ≤ l/8 := by
    have h1 := mul_le_mul_of_nonneg_left hradloss (show 0 ≤ 3*C^2 by positivity)
    have h2 := mul_le_mul_of_nonneg_right hkR.le hl
    nlinarith only [h1,h2]
  have hwell : l*d ≤ 1/16 := by simpa only [show (1:ℝ)/(64*(1/4)) = 1/16 by norm_num] using hprod r hrpos.le
  have hquad := corrugation_high_quadratic_lower (w := ang e') hν0 hν1 hl hrpos hr1 hd hdp
    (mul_nonneg hC.le hR.le) hrade hradt hangt hwell hradsmall
  have hfast : s*Q/2 ≤ ν*F e'+F t := by
    have hb := mul_le_mul_of_nonneg_left hquad (mul_nonneg (mul_nonneg hs.le hJ.le) hχ₀)
    have heq (v : Coord) : F v = s*J*χ₀*(deriv (corrugationSlope amp (1/4)) r*rad v*rad v+(l/r)*ang v*ang v) := by
      dsimp only [F]
      rw [(corrugationPeriodicWell_global_radial_jets amp z (a.prod b v) (a.prod b v) hr0).2]
    rw [heq e',heq t]
    dsimp only [Q]
    nlinarith only [hb]
  have heb (v : Coord) (hv : g x v v = 1) : |Err v| ≤ BE :=
    (herror s L hs.le hL k y hy x hx e he v v hv hv T hT).2 hreg
  have hBE : 0 ≤ BE := (abs_nonneg _).trans (heb e' heu)
  have hE1 := mul_le_mul_of_nonneg_left (abs_le.mp (heb e' heu)).1 hν0
  have hE2 := (abs_le.mp (heb t htu)).1
  have hEν := mul_le_mul_of_nonneg_right hν1 hBE
  have herrorlower : -2*BE ≤ ν*Err e'+Err t := by
    linarith only [hE1,hE2,hEν]
  have herrorSmall : 2*BE ≤ s*Q/4 := by
    have hh := mul_le_mul_of_nonneg_right hkE.le (mul_nonneg hs.le hQ.le)
    dsimp [BE]; nlinarith only [hh]
  have hold1 := mul_le_mul_of_nonneg_left (abs_le.mp (hHbound x hx e' e' heu heu)).1 hν0
  have hold2 := (abs_le.mp (hHbound x hx t t htu htu)).1
  have hold3 := mul_le_mul_of_nonneg_right hν1 hH.le
  have hold : -2*H ≤ ν*sourceHessian g S x e' e'+sourceHessian g S x t t := by
    linarith only [hold1,hold2,hold3]
  have hlarge : 8*H+4 < s*Q := by
    have h1 := mul_lt_mul_of_pos_left hreg hm
    have h2 := mul_le_mul_of_nonneg_right hms hQ.le
    rw [hTm] at h1
    exact h1.trans_le h2
  have hdecomp (v : Coord) : sourceHessian g (S+w) x v v = sourceHessian g S x v v+F v+Err v :=
    corrugated_envelope_global_hessian g S χ (hS.contDiffAt (hU.mem_nhds (hDU hx))) hχ
      amp s hJ.ne' R a b y v v
  have hnew : 1 ≤ ν*sourceHessian g (S+w) x e' e'+sourceHessian g (S+w) x t t := by
    rw [hdecomp e',hdecomp t]
    nlinarith only [hfast,herrorlower,herrorSmall,hold,hlarge]
  exact ⟨hnq,htu,hto,hnew⟩

end
end Yau.Geometry

end OAI
