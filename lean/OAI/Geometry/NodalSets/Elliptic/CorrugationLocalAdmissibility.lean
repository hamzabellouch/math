import OAI.Geometry.NodalSets.Elliptic.CorrugationFixedAmplitude
import OAI.Geometry.NodalSets.Elliptic.CorrugationHighAdmissibility
import OAI.Geometry.NodalSets.Elliptic.CorrugationLowAdmissibility
import OAI.Geometry.NodalSets.Elliptic.NormalizedAdmissibility

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

theorem corrugation_fixed_local_admissibility
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
    {L : ℝ} (hL : 0 < L) :
    ∀ᶠ k : ℕ in atTop,
      ∀ y ∈ D, ∀ x ∈ D, ‖x-y‖ ≤ corrugationScale L k →
      ∀ e : Coord ≃L[ℝ] Coord,
      e (Pi.single 0 1) = (corrugationOldSlope g S y)⁻¹ • metricGradient g S y →
      (∀ i j, g y (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0) →
      (∀ u, g y u u = 1 → g y (metricGradient g S y) u = 0 →
        sourceHessian g S y u u ≤ sourceHessian g S y (e (Pi.single 1 1)) (e (Pi.single 1 1))) →
      let w := localizedCorrugation χ (corrugationPeriodicWell corrugationFixedAmplitude)
        (corrugationOldSlope g S y) (corrugationFrequency k) (corrugationScale L k)
        (frozenFrameCovector e 2) (frozenFrameCovector e 3) y
      let p := metricGradient g (S+w) x
      p ≠ 0 ∧ ∃ t : Coord, g x t t = 1 ∧ g x p t = 0 ∧
        0 < sourceHessian g (S+w) x p p+(g x p p+4)*sourceHessian g (S+w) x t t := by
  obtain ⟨ha,ha1,hprod,_⟩ := corrugationFixedAmplitude_spec
  have hn : ∀ y ∈ D, metricGradient g S y ≠ 0 := fun y hy ↦ (hadm y hy).1
  obtain ⟨c,hc,hlow⟩ := corrugation_actual_low_admissibility g S χ hD hconv hU hDU hg hS hp
    hsym hadm hχ hcpt hχ0 hχ1 hAχ hχA ha.le ha1 hL
  obtain ⟨T,hT,hhigh⟩ := corrugation_actual_high_admissibility g S χ hD hconv hU hDU hg hS hp hn
    hχ hcpt hχ0 hχ1 hAχ hχA ha.le ha1 hL hprod
  have hnv := corrugation_local_nonvanishing g S χ hD hconv hU hDU hg hS hp hn hχ hcpt corrugationFixedAmplitude hL
  filter_upwards [hlow T hT,hhigh,hnv] with k hkl hkh hknv
  intro y hy x hx hxy e he0 he hmax
  dsimp only
  let w := localizedCorrugation χ (corrugationPeriodicWell corrugationFixedAmplitude)
    (corrugationOldSlope g S y) (corrugationFrequency k) (corrugationScale L k)
    (frozenFrameCovector e 2) (frozenFrameCovector e 3) y
  let p := metricGradient g (S+w) x
  have hnP : p ≠ 0 := hknv y hy x hx hxy e he0 he
  have hpP : 0 < g x p p := hp x (hDU hx) p hnP
  refine ⟨hnP,?_⟩
  have finish (t : Coord) (htu : g x t t = 1) (horth : g x (metricNormalize (g x) p) t = 0)
      (hstr : 0 < (g x p p/(g x p p+4))*sourceHessian g (S+w) x (metricNormalize (g x) p)
        (metricNormalize (g x) p)+sourceHessian g (S+w) x t t) :
      ∃ t : Coord, g x t t = 1 ∧ g x p t = 0 ∧
        0 < sourceHessian g (S+w) x p p+(g x p p+4)*sourceHessian g (S+w) x t t := by
    obtain ⟨ho,hs⟩ := normalized_strict_to_direction (g x) (sourceHessian g (S+w) x) p t hpP horth hstr
    exact ⟨t,htu,ho,hs⟩
  let z := corrugationFastMap (corrugationFrequency k) (frozenFrameCovector e 2) (frozenFrameCovector e 3) (x-y)
  rcases le_or_gt (corrugationFrequency k*χ ((corrugationScale L k)⁻¹ • (x-y))*
      corrugationSlope corrugationFixedAmplitude (1/4) (corrugationCellRadius z)) T with hreg | hreg
  · obtain ⟨_,hu,ho,hs⟩ := hkl y hy x hx hxy e he0 he hmax hreg
    exact finish _ hu ho (hc.trans_le hs)
  · obtain ⟨_,hu,ho,hs⟩ := hkh y hy x hx hxy e he0 he hreg
    exact finish _ hu ho (zero_lt_one.trans_le hs)

end
end Yau.Geometry

end OAI
