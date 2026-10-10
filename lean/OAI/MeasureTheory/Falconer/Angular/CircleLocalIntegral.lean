import OAI.MeasureTheory.Falconer.Angular.CircleStationaryPartition
import OAI.MeasureTheory.Falconer.Angular.AngularIntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

noncomputable def circlePositivePiece (Λ : ℝ) (f : ℝ → ℂ) : ℂ :=
  ∫ θ in (-Real.pi)..Real.pi, cosineOscillator Λ θ *
    (stationaryCutoff (stationarySineChart θ):ℂ)*f θ

 theorem stationarySineInverse_mem (u : ℝ) :
    stationarySineInverse u ∈ Icc (-Real.pi) Real.pi := by
  unfold stationarySineInverse
  constructor
  · linarith [Real.neg_pi_div_two_le_arcsin (u/2)]
  · linarith [Real.arcsin_le_pi_div_two (u/2)]

 theorem stationarySineInverse_mono : Monotone stationarySineInverse := by
  intro a b hab
  unfold stationarySineInverse
  have h := Real.arcsin_le_arcsin (show a/2 ≤ b/2 by linarith)
  linarith

 theorem stationaryCutoff_angle_support {θ : ℝ} (hθ : θ ∈ Icc (-Real.pi) Real.pi)
    (hc : stationaryCutoff (stationarySineChart θ) ≠ 0) :
    θ ∈ Ioo (stationarySineInverse (-1)) (stationarySineInverse 1) := by
  have hh : stationarySineChart θ ∈ Function.support (stationaryCutoff : ℝ → ℝ) := hc
  rw [ContDiffBump.support_eq] at hh
  have hu : |stationarySineChart θ| < 1 := by simpa [stationaryCutoff,Real.dist_eq] using hh
  have ha := Real.arcsin_lt_arcsin (by norm_num : (-1:ℝ) ≤ -1/2)
    (show (-1:ℝ)/2 < stationarySineChart θ/2 by linarith [(abs_lt.mp hu).1])
    (show stationarySineChart θ/2 ≤ 1 by linarith [(abs_lt.mp hu).2])
  have hb := Real.arcsin_lt_arcsin
    (show (-1:ℝ) ≤ stationarySineChart θ/2 by linarith [(abs_lt.mp hu).1])
    (show stationarySineChart θ/2 < (1:ℝ)/2 by linarith [(abs_lt.mp hu).2]) (by norm_num)
  have he := stationarySineInverse_chart hθ
  unfold stationarySineInverse at he ⊢
  constructor <;> linarith

 theorem circlePositivePiece_localized (Λ : ℝ) (f : ℝ → ℂ) :
    circlePositivePiece Λ f = localizedCircleIntegral Λ f := by
  let F : ℝ → ℂ := fun θ => cosineOscillator Λ θ *
    (stationaryCutoff (stationarySineChart θ):ℂ)*f θ
  let P : ℝ → ℂ := (Ioc (-Real.pi) Real.pi).indicator F
  have hP : Function.support P ⊆ Ioc (stationarySineInverse (-1)) (stationarySineInverse 1) := by
    intro θ hθ
    have ht : θ ∈ Ioc (-Real.pi) Real.pi := by
      by_contra hh
      exact hθ (indicator_of_notMem hh F)
    have hc : stationaryCutoff (stationarySineChart θ) ≠ 0 := by
      intro hh
      exact hθ (by simp [P,F,ht,hh])
    have h := stationaryCutoff_angle_support ⟨ht.1.le,ht.2⟩ hc
    exact ⟨h.1,h.2.le⟩
  have he : (∫ θ : ℝ, P θ) = circlePositivePiece Λ f := by
    rw [integral_indicator measurableSet_Ioc]
    exact (intervalIntegral.integral_of_le (neg_le_self Real.pi_pos.le)).symm
  rw [← he,← intervalIntegral.integral_eq_integral_of_support_subset hP]
  change (∫ θ in stationarySineInverse (-1)..stationarySineInverse 1, P θ) =
    ∫ θ in stationarySineInverse (-1)..stationarySineInverse 1, F θ
  apply intervalIntegral.integral_congr_ae
  filter_upwards with θ hθ
  have hθ' : θ ∈ Ioc (stationarySineInverse (-1)) (stationarySineInverse 1) := by
    simpa only [uIoc_of_le (stationarySineInverse_mono (by norm_num : (-1:ℝ) ≤ 1))] using hθ
  have ht : θ ∈ Ioc (-Real.pi) Real.pi :=
    ⟨(stationarySineInverse_mem (-1)).1.trans_lt hθ'.1,hθ'.2.trans (stationarySineInverse_mem 1).2⟩
  exact indicator_of_mem ht F

end PlanarFalconer

end OAI
