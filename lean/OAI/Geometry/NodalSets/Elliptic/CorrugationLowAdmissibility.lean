import OAI.Geometry.NodalSets.Elliptic.CorrugationFastLower
import OAI.Geometry.NodalSets.Elliptic.CorrugationLowOldMargin
import OAI.Geometry.NodalSets.Elliptic.CorrugationLowRadial
import OAI.Geometry.NodalSets.Elliptic.CorrugationRadialLoss
import OAI.Geometry.NodalSets.Elliptic.CorrugationUnitRegimeErrors

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

theorem corrugation_actual_low_admissibility
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (S χ : Coord → ℝ)
    {D U : Set Coord} (hD : IsCompact D) (hconv : Convex ℝ D)
    (hU : IsOpen U) (hDU : D ⊆ U)
    (hg : ContDiffOn ℝ ∞ g U) (hS : ContDiffOn ℝ ∞ S U)
    (hp : ∀ y ∈ U, ∀ v, v ≠ 0 → 0 < g y v v)
    (hsym : ∀ y ∈ D, ∀ u v, g y u v = g y v u)
    (hadm : ∀ y ∈ D, metricGradient g S y ≠ 0 ∧
      ∃ q : Coord, g y q q = 1 ∧ g y (metricGradient g S y) q = 0 ∧
        0 < sourceHessian g S y (metricGradient g S y) (metricGradient g S y) +
          (g y (metricGradient g S y) (metricGradient g S y)+4)*sourceHessian g S y q q)
    (hχ : ContDiff ℝ ∞ χ) (hcpt : HasCompactSupport χ)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1)
    {Aχ : ℝ} (hAχ : 0 < Aχ)
    (hχA : ∀ z, ‖fderiv ℝ χ z‖ ≤ Aχ*(χ z)^((7:ℝ)/8))
    {amp L : ℝ} (ha : 0 ≤ amp) (ha1 : amp ≤ 1) (hL : 0 < L) :
    ∃ c : ℝ, 0 < c ∧ ∀ T : ℝ, 0 < T → ∀ᶠ k : ℕ in atTop,
      ∀ y ∈ D, ∀ x ∈ D, ‖x-y‖ ≤ corrugationScale L k →
      ∀ e : Coord ≃L[ℝ] Coord,
      e (Pi.single 0 1) = (corrugationOldSlope g S y)⁻¹ • metricGradient g S y →
      (∀ i j, g y (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0) →
      (∀ u, g y u u = 1 → g y (metricGradient g S y) u = 0 →
        sourceHessian g S y u u ≤ sourceHessian g S y (e (Pi.single 1 1)) (e (Pi.single 1 1))) →
      let z := corrugationFastMap (corrugationFrequency k) (frozenFrameCovector e 2) (frozenFrameCovector e 3) (x-y)
      let p := metricGradient g (S+localizedCorrugation χ (corrugationPeriodicWell amp)
        (corrugationOldSlope g S y) (corrugationFrequency k) (corrugationScale L k)
        (frozenFrameCovector e 2) (frozenFrameCovector e 3) y) x
      let q := metricPerpProjection (g x) (metricNormalize (g x) p) (e (Pi.single 1 1))
      let t := metricNormalize (g x) q
      corrugationFrequency k*χ ((corrugationScale L k)⁻¹ • (x-y))*
        corrugationSlope amp (1/4) (corrugationCellRadius z) ≤ T →
      q ≠ 0 ∧ g x t t = 1 ∧ g x (metricNormalize (g x) p) t = 0 ∧
        c ≤ (g x p p/(g x p p+4))*sourceHessian g (S+localizedCorrugation χ (corrugationPeriodicWell amp)
          (corrugationOldSlope g S y) (corrugationFrequency k) (corrugationScale L k)
          (frozenFrameCovector e 2) (frozenFrameCovector e 3) y) x (metricNormalize (g x) p)
          (metricNormalize (g x) p)+sourceHessian g (S+localizedCorrugation χ (corrugationPeriodicWell amp)
          (corrugationOldSlope g S y) (corrugationFrequency k) (corrugationScale L k)
          (frozenFrameCovector e 2) (frozenFrameCovector e 3) y) x t t := by
  have hn : ∀ y ∈ D, metricGradient g S y ≠ 0 := fun y hy ↦ (hadm y hy).1
  obtain ⟨c,hc,hmargin⟩ := corrugation_actual_low_old_margin g S χ hD hconv hU hDU
    hg hS hp hsym hadm hχ hcpt hχ0 hχ1 ha ha1 hL
  obtain ⟨m,hm,B,hB,hslope⟩ := corrugationOldSlope_compact_bounds g S hD hU hDU hg hS hp hn
  obtain ⟨E,hE,herror⟩ := corrugation_actual_metric_unit_errors g χ hD hU hDU hg hp hχ hcpt
    (fun z ↦ ⟨hχ0 z,hχ1 z⟩) hAχ hχA ha ha1
  obtain ⟨D₀,hD₀,hloss⟩ := corrugation_actual_radial_loss
  have hnv := corrugation_local_nonvanishing g S χ hD hconv hU hDU hg hS hp hn hχ hcpt amp hL
  refine ⟨c/2,half_pos hc,?_⟩
  intro T hT
  obtain ⟨C,hC,hrad⟩ := corrugation_actual_low_radial g S χ hD hconv hU hDU hg hS hp hn
    hχ hcpt hχ0 hχ1 ha ha1 hL T
  have hlim := corrugation_low_rates_tendsto hL.ne' hT.le
  have hsmall : Tendsto (fun k ↦ 2*(B*C^2*D₀*corrugationLowRadialRate L T k)+
      2*(E*B*corrugationLowErrorRate L T k)) atTop (𝓝 0) := by
    simpa using ((hlim.2.const_mul (B*C^2*D₀)).const_mul 2).add ((hlim.1.const_mul (E*B)).const_mul 2)
  filter_upwards [hmargin T,hrad,hnv,hsmall.eventually_lt_const (half_pos hc)] with k hkm hkr hknv hks
  intro y hy x hx hxy e he0 he hmax
  dsimp only
  intro hreg
  let s := corrugationOldSlope g S y
  let J := corrugationFrequency k
  let R := corrugationScale L k
  let a := frozenFrameCovector e 2
  let b := frozenFrameCovector e 3
  let z := corrugationFastMap J a b (x-y)
  let χ₀ := χ (R⁻¹ • (x-y))
  let w := localizedCorrugation χ (corrugationPeriodicWell amp) s J R a b y
  let p := metricGradient g (S+w) x
  let e' := metricNormalize (g x) p
  let q := metricPerpProjection (g x) e' (e (Pi.single 1 1))
  let t := metricNormalize (g x) q
  let ν := g x p p/(g x p p+4)
  let d := max (-deriv (corrugationSlope amp (1/4)) (corrugationCellRadius z)) 0
  let F : Coord → ℝ := fun v ↦ s*J*χ₀*
    fderiv ℝ (fderiv ℝ (corrugationPeriodicWell amp)) z (a.prod b v) (a.prod b v)
  let Err : Coord → ℝ := fun v ↦ corrugationMetricError g χ (corrugationPeriodicWell amp) s J R a b y x v v
  let BF := B*C^2*D₀*corrugationLowRadialRate L T k
  let BE := E*B*corrugationLowErrorRate L T k
  have hs : 0 < s := corrugationOldSlope_positive g S y (hp y (hDU hy)) (hn y hy)
  have hsB : s ≤ B := (hslope y hy).2
  have hJ : 0 < J := corrugationFrequency_positive k
  have hR : 0 < R := corrugationScale_positive hL k
  have hχ₀ : 0 ≤ χ₀ := hχ0 _
  have hd : 0 ≤ d := le_max_right _ _
  have hlr : 0 ≤ corrugationLowRadialRate L T k := by
    unfold corrugationLowRadialRate; positivity
  have her : 0 ≤ corrugationLowErrorRate L T k := by
    unfold corrugationLowErrorRate; positivity
  have hBF : 0 ≤ BF := by dsimp [BF]; positivity
  have hBE : 0 ≤ BE := by dsimp [BE]; positivity
  obtain ⟨hnq,htu,hto,hold⟩ := hkm y hy x hx hxy e he0 he hmax hreg
  have hp0 : 0 < g x p p := hp x (hDU hx) p (hknv y hy x hx hxy e he0 he)
  have heu : g x e' e' = 1 := metricNormalize_unit (g x) p hp0
  have hν0 : 0 ≤ ν := div_nonneg hp0.le (by positivity)
  have hν1 : ν ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  have hradial : R^2*J*χ₀*d ≤ D₀*corrugationLowRadialRate L T k :=
    (hloss amp (corrugationCellRadius z) χ₀ L T ha ha1 (corrugationCellRadius_properties z).1
      hχ₀ (hχ1 _) hL hT k).1 hreg
  have hfb (v : Coord) (hv : corrugationCellRadius z ≠ 0 →
      |radialComponent (corrugationCellPoint z) (a.prod b v) (corrugationCellRadius z)| ≤ C*R) : -BF ≤ F v := by
    have hf := mul_le_mul_of_nonneg_left (corrugation_fast_hessian_lower ha (mul_nonneg hC.le hR.le) z (a.prod b v) hv)
      (mul_nonneg (mul_nonneg hs.le hJ.le) hχ₀)
    have hrb := mul_le_mul_of_nonneg_left hradial (mul_nonneg hs.le (sq_nonneg C))
    have hsb := mul_le_mul_of_nonneg_right hsB
      (mul_nonneg (mul_nonneg (sq_nonneg C) hD₀.le) hlr)
    change -(B*C^2*D₀*corrugationLowRadialRate L T k) ≤ F v
    change s*J*χ₀*(-(d*(C*R)^2)) ≤ F v at hf
    nlinarith only [hf,hrb,hsb]
  have hfe : -BF ≤ F e' := hfb e' (by
    intro hr
    rw [frozen_radial_covector (g y) e he]
    exact (hkr y hy x hx hxy e he0 he hr hreg).1)
  have hft : -BF ≤ F t := hfb t (by
    intro hr
    rw [frozen_radial_covector (g y) e he]
    exact (hkr y hy x hx hxy e he0 he hr hreg).2)
  have heb (v : Coord) (hv : g x v v = 1) : |Err v| ≤ BE := by
    have hb := (herror s L hs.le hL k y hy x hx e he v v hv hv T hT).1 hreg
    exact hb.trans (by dsimp [BE]; gcongr)
  have hdecomp (v : Coord) : sourceHessian g (S+w) x v v = sourceHessian g S x v v+F v+Err v :=
    corrugated_envelope_global_hessian g S χ (hS.contDiffAt (hU.mem_nhds (hDU hx))) hχ
      amp s hJ.ne' R a b y v v
  have hbound := weighted_hessian_perturbation_lower
    (H₁ := sourceHessian g S x e' e') (H₂ := sourceHessian g S x t t) hν0 hν1 hBF hBE hfe hft (heb e' heu) (heb t htu)
  have hnew : c/2 ≤ ν*sourceHessian g (S+w) x e' e'+sourceHessian g (S+w) x t t := by
    rw [hdecomp e',hdecomp t]
    change c ≤ ν*sourceHessian g S x e' e'+sourceHessian g S x t t at hold
    change 2*BF+2*BE < c/2 at hks
    linarith
  exact ⟨hnq,htu,hto,hnew⟩

end
end Yau.Geometry

end OAI
