import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.FineSmearingPotential
import OAI.Analysis.CoulombIonization.RadialBounds.TranslatedShortRange

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal

namespace CoulombNeumann
open CoulombAtom CoulombAnalysis

lemma varthetaScaled_local_potential_le {b q : ℝ} (hb : 0 < b)
    (y a : Space) (ha : a ≠ y) :
    (∫ z in ball y q, varthetaScaled b (z-a)/‖y-z‖) ≤
      (ball y (q+Real.sqrt 3*b)).indicator (fun z => 1/‖y-z‖) a := by
  by_cases hnear : a ∈ ball y (q+Real.sqrt 3*b)
  · rw [indicator_of_mem hnear]
    calc
      _ ≤ ∫ z : Space, varthetaScaled b (z-a)/‖y-z‖ :=
        setIntegral_le_integral
          (translated_pole_integrable (varthetaScaled_integrable hb) (varthetaScaled_memLp hb) y a)
          (Eventually.of_forall fun z => div_nonneg (varthetaScaled_nonneg hb _) (norm_nonneg _))
      _ = tfPotential (varthetaScaled b) (y-a) := integral_translated_pole _ _ _
      _ ≤ _ := varthetaScaled_potential_le hb (sub_ne_zero.mpr ha.symm)
  · rw [indicator_of_notMem hnear]
    apply le_of_eq
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    have hzero : varthetaScaled b (z-a) = 0 := by
      by_contra hne
      have hs := varthetaScaled_support_bound hb (z-a) hne
      have hd := dist_triangle a z y
      have hfar : q+Real.sqrt 3*b ≤ dist a y := le_of_not_gt hnear
      have hclose : dist z y < q := hz
      rw [←dist_eq_norm,dist_comm z a] at hs
      linarith
    simp only [hzero,zero_div,Pi.zero_apply]

lemma retainedSmear_local_potential_le {N : ℕ} {b q : ℝ} (hb : 0 < b)
    (S : Finset (Fin N)) (x : Configuration N) (y : Space)
    (hxy : ∀ i ∈ S, x i ≠ y) :
    (∫ z in ball y q, retainedSmear b S x z/‖y-z‖) ≤
      ∑ i ∈ S, (ball y (q+Real.sqrt 3*b)).indicator (fun z => 1/‖y-z‖) (x i) := by
  simp only [retainedSmear,Finset.sum_div]
  rw [integral_finsetSum _ (fun i _ =>
    (translated_pole_integrable (varthetaScaled_integrable hb) (varthetaScaled_memLp hb) y (x i)).restrict)]
  exact Finset.sum_le_sum (fun i hi => varthetaScaled_local_potential_le hb y (x i) (hxy i hi))

theorem retainedPatchLp_local_potential_le {N : ℕ} {b q R : ℝ} (hb : 0 < b) (hqR : q ≤ R)
    (S : Finset (Fin N)) (x : Configuration N) (y : Space)
    (hxy : ∀ i ∈ S, x i ≠ y) :
    (∫ z in ball 0 q, ‖retainedPatchLp hb S x y R z‖/‖z‖) ≤
      ∑ i ∈ S, (ball y (q+Real.sqrt 3*b)).indicator (fun z => 1/‖y-z‖) (x i) := by
  have he := ae_mono (Measure.restrict_mono (ball_subset_ball hqR) le_rfl)
    (retainedPatchLp_ae hb S x y R)
  have hid : (∫ z in ball 0 q, ‖retainedPatchLp hb S x y R z‖/‖z‖) =
      ∫ z in ball 0 q, retainedSmear b S x (y+z)/‖z‖ := by
    apply integral_congr_ae
    filter_upwards [he] with z hz
    rw [hz,Real.norm_of_nonneg (retainedSmear_nonneg hb S x _)]
  rw [hid]
  have ht := setIntegral_translate_ball y q (fun z => retainedSmear b S x z/‖y-z‖)
  simp only [sub_add_cancel_left,norm_neg] at ht
  rw [ht]
  exact retainedSmear_local_potential_le hb S x y hxy

end CoulombNeumann

end

end OAI
