import OAI.Geometry.RCD.Heat.BoundedHeatGram
import OAI.Geometry.RCD.Sobolev.SobolevGramPolarization

namespace OAI

/-! # Mixed Sobolev Gram entries for two actual positive-time heat factors

A common earlier heat time and polarization handle distinct times. Only
the two original bounded-amplitude hypotheses are used.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (Q : QuadraticCheegerEnergy μ)

theorem heatSobolev_split (f : Lp ℝ 2 μ) {r t : ℝ}
    (hr : 0 < r) (ht : 0 < t) (hrt : r < t) :
    heatSobolev μ Q r hr (heatAt μ Q (t-r) f) = heatSobolev μ Q t ht f := by
  apply Subtype.ext
  change heatAt μ Q r (heatAt μ Q (t-r) f) = heatAt μ Q t f
  rw [← mul_apply_eq_comp,← heatAt_add μ Q r (t-r) hr.le (sub_nonneg.mpr hrt.le)]
  congr 2
  ring

namespace NoncollapsedRCD
variable {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  [(hausdorff n X).Regular] [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] (hn : 2 ≤ n) (p : X)

include hn p in
theorem bounded_heat_mixed_gram (f g : Lp ℝ 2 (hausdorff n X)) (A B : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x| ≤ A) (hg : ∀ᵐ x ∂hausdorff n X, |g x| ≤ B)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    ∃ G : SobolevSpace (hausdorff n X) hX.quadratic,
      SobolevSpace.toLp (hausdorff n X) hX.quadratic G =ᵐ[hausdorff n X]
        localGamma (hausdorff n X) hX.quadratic
          (heatSobolev (hausdorff n X) hX.quadratic s hs f)
          (heatSobolev (hausdorff n X) hX.quadratic t ht g) := by
  let μ := hausdorff n X
  let Q := hX.quadratic
  let r := min s t/2
  have hr : 0 < r := half_pos (lt_min hs ht)
  have hrs : r<s := (half_lt_self (lt_min hs ht)).trans_le (min_le_left s t)
  have hrt : r<t := (half_lt_self (lt_min hs ht)).trans_le (min_le_right s t)
  let F := heatAt μ Q (s-r) f
  let H := heatAt μ Q (t-r) g
  have hF : ∀ᵐ x ∂μ, |F x| ≤ A := heatAt_abs_le_const μ Q (s-r) A f hf
  have hH : ∀ᵐ x ∂μ, |H x| ≤ B := heatAt_abs_le_const μ Q (t-r) B g hg
  have hsum : ∀ᵐ x ∂μ, |(F+H) x| ≤ (A+B:ℝ≥0) := by
    filter_upwards [hF,hH,Lp.coeFn_add F H] with x hf hg he
    rw [he]
    exact (abs_add_le _ _).trans (add_le_add hf hg)
  obtain ⟨Gf,hGf⟩ := hX.bounded_heat_gram hn p F A hF hr
  obtain ⟨Gh,hGh⟩ := hX.bounded_heat_gram hn p H B hH hr
  obtain ⟨Gs,hGs⟩ := hX.bounded_heat_gram hn p (F+H) (A+B) hsum hr
  have he : heatSobolev μ Q r hr (F+H) = heatSobolev μ Q r hr F+heatSobolev μ Q r hr H :=
    (heatSobolevMap μ Q r hr).map_add F H
  rw [he] at hGs
  have hpol := sobolev_gram_polarization μ Q (heatSobolev μ Q r hr F)
    (heatSobolev μ Q r hr H) Gf Gh Gs hGf hGh hGs
  rw [heatSobolev_split μ Q f hr hs hrs,heatSobolev_split μ Q g hr ht hrt] at hpol
  exact ⟨_,hpol⟩

end NoncollapsedRCD
end RegularPointCoordinates

end

end OAI
