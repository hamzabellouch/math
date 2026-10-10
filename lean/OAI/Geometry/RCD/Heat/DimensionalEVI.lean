import OAI.Geometry.RCD.Transport.DimensionalSlope

namespace OAI

/-! # Integrated dimensional EVI for the actual heat flow

This is the squared-distance rate form of EKS (2.20), for compact bounded
reference densities. The entropy ratio is retained exactly.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X]

theorem NoncollapsedRCD.bounded_heat_dimensional_EVI
    (K : ℝ) (n : ℕ) [IsLocallyFiniteMeasure (hausdorff n X)] (hn : 2 ≤ n)
    (hX : NoncollapsedRCD K n X) (hK : K ≤ 0) {N : ℝ} (hN : (n:ℝ) ≤ N) (p : X)
    (f : Lp ℝ 2 (hausdorff n X)) (C : ℝ≥0) (hf0 : 0 ≤ f)
    (hfC : ∀ᵐ x ∂hausdorff n X, f x ≤ C)
    (hfm : ∫x, f x ∂hausdorff n X = 1)
    {r : ℝ} (hfs : ∀ᵐ x ∂hausdorff n X, f x ≠ 0 → dist p x ≤ r)
    (ν : Measure X) [IsProbabilityMeasure ν] (hν : ν ≤ ENNReal.ofReal C • hausdorff n X)
    {rν : ℝ} (hνS : ∀ᵐ x ∂ν, dist x p ≤ rν) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ((wassersteinSq (heatMeasure (hausdorff n X) hX.quadratic b f) ν).toReal-
      (wassersteinSq (heatMeasure (hausdorff n X) hX.quadratic a f) ν).toReal)/2 ≤
      ∫t in a..b, entropyPowerRate N
        (-(K*(wassersteinSq (heatMeasure (hausdorff n X) hX.quadratic t f) ν).toReal/N))
        (Real.exp (-boltzmannEntropy (hausdorff n X) (heatMeasure (hausdorff n X) hX.quadratic t f)/N))
        (Real.exp (-boltzmannEntropy (hausdorff n X) ν/N)) := by
  let μ := hausdorff n X
  let D : ℝ → ℝ := fun s => (wassersteinSq (heatMeasure μ hX.quadratic s f) ν).toReal
  let E : ℝ → ℝ := fun s => boltzmannEntropy μ (heatMeasure μ hX.quadratic s f)
  let G : ℝ → ℝ := fun s => entropyPowerRate N (-(K*D s/N))
    (Real.exp (-E s/N)) (Real.exp (-boltzmannEntropy μ ν/N))
  have hfabs : ∀ᵐ x ∂μ, |f x| ≤ C := by
    filter_upwards [(Lp.coeFn_nonneg _).mpr hf0,hfC] with x hl hu
    simpa only [abs_of_nonneg hl] using hu
  have hνac : ν ≪ μ := (Measure.absolutelyContinuous_of_le hν).trans Measure.smul_absolutelyContinuous
  have hν2 := finiteSecondMoment_of_ae_dist_le ν p hνS
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hN0 : 0 < N := by linarith
  have hnn (s : ℝ) : 0 ≤ -(K*D s/N) := neg_nonneg.mpr
    (div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hK ENNReal.toReal_nonneg) hN0.le)
  have hDc {t : ℝ} (ht : 0 < t) : ContinuousAt D t :=
    hX.heat_wassersteinSq_continuousAt K n hn p f hf0 ⟨r,hfs⟩ hfm C hfabs ν hνac hν2 ht
  have hGc : ContinuousOn G (Ioi 0) := by
    intro t ht
    have hEt : ContinuousAt E t := hX.heat_entropy_continuousAt K n hn p f hf0 ⟨r,hfs⟩ ht
    have hc : ContinuousAt G t := tendsto_entropyPowerRate hnn (hnn t) (Real.exp_ne_zero _)
      (((hDc ht).tendsto.const_mul K).div_const N).neg
      (Real.continuous_exp.tendsto _ |>.comp (hEt.tendsto.neg.div_const N)) tendsto_const_nhds
    exact hc.continuousWithinAt
  have hs := integral_bound_of_frequent_right_slopes (D := fun t => D t/2) (G := G) ha hab
    (fun t ht => ((hDc (ha.trans_le ht.1)).div_const 2).continuousWithinAt) hGc (by
      intro t ht z hz
      exact hX.bounded_heat_frequent_dimensional_slope K n hn hK hN p f C hf0 hfC hfm hfs ν hν hνS
        (ha.trans_le ht.1) z hz)
  change (D b-D a)/2 ≤ ∫t in a..b, G t
  linarith only [hs]

end RegularPointCoordinates

end

end OAI
