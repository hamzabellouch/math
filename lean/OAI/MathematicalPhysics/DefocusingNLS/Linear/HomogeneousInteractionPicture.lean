import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousDuhamel
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace OAI

/-! # Differentiation in the free interaction picture

Removing the exact free group from a forced mild trajectory leaves the
ordinary integral of the transported source. Its derivative exists in Y
for continuous forcing, without additional spatial regularity.
-/

open MeasureTheory Set

namespace DefocusingNLS

attribute [local irreducible] homogeneousFreeOperator

noncomputable def homogeneousForcedTrajectory (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (f : HomogeneousY a k) (r : ℝ → HomogeneousY a k) (t : ℝ) : HomogeneousY a k :=
  homogeneousFreeOperator a b k t ha ha1 hk f + homogeneousDuhamel a b k ha ha1 hk t r

theorem continuous_homogeneousForcedTrajectory (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (f : HomogeneousY a k) (r : ℝ → HomogeneousY a k) (hr : Continuous r) :
    Continuous (homogeneousForcedTrajectory a b k ha ha1 hk f r) := by
  exact ((continuous_homogeneousFreeOperator_uncurry a b k ha ha1 hk).comp
    (continuous_id.prodMk continuous_const)).add
      (continuous_homogeneousDuhamel a b k ha ha1 hk r hr)

@[simp] theorem homogeneousForcedTrajectory_zero (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (f : HomogeneousY a k) (r : ℝ → HomogeneousY a k) :
    homogeneousForcedTrajectory a b k ha ha1 hk f r 0 = f := by
  simp [homogeneousForcedTrajectory, homogeneousDuhamel]

theorem homogeneousDuhamel_pullback (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (r : ℝ → HomogeneousY a k) (hr : Continuous r) (t : ℝ) :
    homogeneousFreeOperator a b k (-t) ha ha1 hk (homogeneousDuhamel a b k ha ha1 hk t r) =
      ∫ τ in (0 : ℝ)..t, homogeneousFreeOperator a b k (-τ) ha ha1 hk (r τ) := by
  have hc : Continuous (fun τ => homogeneousFreeOperator a b k (t - τ) ha ha1 hk (r τ)) :=
    (continuous_homogeneousFreeOperator_uncurry a b k ha ha1 hk).comp
      ((continuous_const.sub continuous_id).prodMk hr)
  unfold homogeneousDuhamel
  rw [← (homogeneousFreeOperator a b k (-t) ha ha1 hk).intervalIntegral_comp_comm
    (hc.intervalIntegrable _ _)]
  apply intervalIntegral.integral_congr
  intro τ _hτ
  dsimp only
  rw [← homogeneousFreeOperator_add, show -t + (t - τ) = -τ by abel]

theorem homogeneousForcedTrajectory_pullback (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (f : HomogeneousY a k) (r : ℝ → HomogeneousY a k) (hr : Continuous r) (t : ℝ) :
    homogeneousFreeOperator a b k (-t) ha ha1 hk
      (homogeneousForcedTrajectory a b k ha ha1 hk f r t) =
        f + ∫ τ in (0 : ℝ)..t, homogeneousFreeOperator a b k (-τ) ha ha1 hk (r τ) := by
  rw [homogeneousForcedTrajectory, map_add, homogeneousFreeOperator_neg_cancel,
    homogeneousDuhamel_pullback a b k ha ha1 hk r hr]

theorem hasDerivAt_homogeneousForcedTrajectory_pullback (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (f : HomogeneousY a k) (r : ℝ → HomogeneousY a k) (hr : Continuous r) (t : ℝ) :
    HasDerivAt (fun s => homogeneousFreeOperator a b k (-s) ha ha1 hk
      (homogeneousForcedTrajectory a b k ha ha1 hk f r s))
      (homogeneousFreeOperator a b k (-t) ha ha1 hk (r t)) t := by
  have hc : Continuous (fun τ => homogeneousFreeOperator a b k (-τ) ha ha1 hk (r τ)) :=
    (continuous_homogeneousFreeOperator_uncurry a b k ha ha1 hk).comp
      (continuous_neg.prodMk hr)
  have hd := (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter (hc.continuousAt (x := t))).const_add f
  convert hd using 1
  funext s
  exact homogeneousForcedTrajectory_pullback a b k ha ha1 hk f r hr s

end DefocusingNLS

end OAI
