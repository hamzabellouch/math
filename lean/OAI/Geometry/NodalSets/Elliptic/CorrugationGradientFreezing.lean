import OAI.Geometry.NodalSets.Coefficients.CorrugationFirstResidual
import OAI.Geometry.NodalSets.Coefficients.MetricGradientResidual

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
open scoped ContDiff
noncomputable section

theorem corrugation_gradient_freezing
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (S χ : Coord → ℝ)
    {D U : Set Coord} (hD : IsCompact D) (hconv : Convex ℝ D)
    (hU : IsOpen U) (hDU : D ⊆ U)
    (hg : ContDiffOn ℝ ∞ g U) (hS : ContDiffOn ℝ ∞ S U)
    (hp : ∀ y ∈ U, ∀ v, v ≠ 0 → 0 < g y v v)
    (hn : ∀ y ∈ D, metricGradient g S y ≠ 0)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1)
    {amp : ℝ} (ha : 0 ≤ amp) (ha1 : amp ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (J R : ℝ), 0 < J → 0 < R →
      ∀ y ∈ D, ∀ x ∈ D, ‖x-y‖ ≤ R →
      ∀ e : Coord ≃L[ℝ] Coord,
      e (Pi.single 0 1) = (corrugationOldSlope g S y)⁻¹ • metricGradient g S y →
      (∀ i j, g y (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0) →
      ‖metricGradient g (S+localizedCorrugation χ (corrugationPeriodicWell amp)
        (corrugationOldSlope g S y) J R (frozenFrameCovector e 2) (frozenFrameCovector e 3) y) x -
        corrugationOldSlope g S y • corrugationLeadingVector amp (χ (R⁻¹ • (x-y))) e
          (corrugationFastMap J (frozenFrameCovector e 2) (frozenFrameCovector e 3) (x-y))‖ ≤
        corrugationOldSlope g S y*C*(R+1/(J*R)) := by
  obtain ⟨m,hm,B,hB,hslope⟩ := corrugationOldSlope_compact_bounds g S hD hU hDU hg hS hp hn
  obtain ⟨c,hc0,M,hM,hmetric⟩ := compact_metric_comparison g hD (hg.continuousOn.mono hDU)
    (fun y hy ↦ hp y (hDU hy))
  obtain ⟨A,hA,hdf⟩ := smooth_compact_covector_freezing S hD hconv hU hDU hS
  obtain ⟨G,hG,hgf⟩ := smooth_compact_freezing g hD hconv hU hDU hg
  obtain ⟨C,hC,hres⟩ := corrugation_frozen_differential_bound g S χ hχ hc amp
  let K : ℝ := 5*(1+c⁻¹)
  let Q : ℝ := A/m+G*K+C
  have hK : 0 < K := by dsimp [K]; positivity
  have hQ : 0 < Q := by dsimp [Q]; positivity
  refine ⟨Q/c,div_pos hQ hc0,?_⟩
  intro J R hJ hR y hy x hx hxy e he0 he
  let s : ℝ := corrugationOldSlope g S y
  let q : Coord := s • corrugationLeadingVector amp (χ (R⁻¹ • (x-y))) e
    (corrugationFastMap J (frozenFrameCovector e 2) (frozenFrameCovector e 3) (x-y))
  have hs : 0 < s := corrugationOldSlope_positive g S y (hp y (hDU hy)) (hn y hy)
  have hms : m ≤ s := (hslope y hy).1
  have hq : ‖q‖ ≤ s*K := by
    dsimp [q]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hs]
    exact mul_le_mul_of_nonneg_left
      (corrugationLeadingVector_bound (g y) hc0 (hmetric y hy).2 ha ha1 (hχ0 _) (hχ1 _) e he _) hs.le
  have hres' := hres J R A hJ hR hA.le y x (hp y (hDU hy)) (hn y hy)
    ((hS.contDiffAt (hU.mem_nhds (hDU hx))).differentiableAt (by simp)) hxy
    (hdf x hx y hy) e he0 he
  have hgrad := metricGradient_frozen_residual_bound g
    (S+localizedCorrugation χ (corrugationPeriodicWell amp) s J R
      (frozenFrameCovector e 2) (frozenFrameCovector e 3) y)
    x y q hc0 hG.le hR.le (mul_nonneg hs.le hK.le) (hmetric x hx).2
    ((hgf x hx y hy).trans (mul_le_mul_of_nonneg_left hxy hG.le)) hq hres'
  have hAs : A ≤ s*(A/m) := by
    have h := mul_le_mul_of_nonneg_right hms (div_nonneg hA.le hm.le)
    have hid : m*(A/m) = A := by field_simp
    rwa [hid] at h
  have hmain : A*R+s/(J*R)*C+G*R*(s*K) ≤ s*Q*(R+1/(J*R)) := by
    have hr0 : 0 ≤ 1/(J*R) := by positivity
    have h1 := mul_le_mul_of_nonneg_right hAs hR.le
    have h2 : 0 ≤ s*C*R := by positivity
    have h3 : 0 ≤ s*(A/m+G*K)*(1/(J*R)) := by positivity
    dsimp [Q]
    simp only [div_eq_mul_inv, one_mul] at *
    nlinarith only [h1,h2,h3]
  calc
    _ ≤ (A*R+s/(J*R)*C+G*R*(s*K))/c := hgrad
    _ ≤ (s*Q*(R+1/(J*R)))/c := div_le_div_of_nonneg_right hmain hc0.le
    _ = s*(Q/c)*(R+1/(J*R)) := by ring

end
end Yau.Geometry

end OAI
