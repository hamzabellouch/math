import Mathlib
import OAI.Analysis.CoulombIonization.FormDomain.WeakMaximum

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric Laplacian
open scoped BigOperators ContDiff Topology

namespace CoulombAnalysis
open CoulombAtom

lemma weak_harmonic_packet_mean_zero {u : Space → ℝ} (hu : Continuous u)
    {R S : ℝ} (hR : 0 < R) (hRS : R < S)
    (hw : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ ball 0 S → (∫ x, u x*Δ g x) = 0) :
    (∫ x, packetDensity 0 R x*u x) = u 0 := by
  let r : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have hr (n : ℕ) : 0 < r n := by dsimp [r]; positivity
  have hr0 : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have havg : Tendsto (fun n => ∫ x, packetDensity 0 (r n) x*u x) atTop (𝓝 (u 0)) :=
    shrinking_density_test_limit (fun n => packetDensity_continuous 0 (r n))
      (fun n => packetDensity_compact 0 (hr n)) (fun n => packetDensity_nonneg 0 (r n))
      (fun n => packetDensity_mass 0 (hr n))
      (fun n x hx => by simpa only [sub_zero] using packetDensity_support 0 (hr n) hx) hr0 hu
  have he : ∀ᶠ n in atTop, (∫ x, packetDensity 0 (r n) x*u x) = ∫ x, packetDensity 0 R x*u x := by
    filter_upwards [hr0.eventually (gt_mem_nhds hR)] with n hn
    have hh := hw (newtonComparisonTest (r n) R) (newtonComparisonTest_smooth (hr n) hR)
      (newtonComparisonTest_compact (hr n) hR)
      ((newtonComparisonTest_tsupport (hr n) hR hn.le).trans (closedBall_subset_ball hRS))
    rw [newtonComparisonTest_pairing (hr n) hR hu] at hh
    have hp := Real.pi_pos
    nlinarith
  exact (tendsto_nhds_unique (havg.congr' he) tendsto_const_nhds).symm

lemma weak_harmonic_packet_mean {u : Space → ℝ} (hu : Continuous u)
    (y : Space) {R S : ℝ} (hR : 0 < R) (hRS : R < S)
    (hw : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ ball y S → (∫ x, u x*Δ g x) = 0) :
    (∫ x, packetDensity y R x*u x) = u y := by
  have hh := weak_harmonic_packet_mean_zero (u := fun x => u (y+x))
    (hu.comp (continuous_const.add continuous_id)) hR hRS (fun g hg hcg hs => ?_)
  · have hm : (∫ x, packetDensity y R x*u x) = ∫ x, packetDensity 0 R x*u (y+x) := by
      have he := integral_add_left_eq_self (μ := volume) (fun x => packetDensity y R x*u x) y
      simpa only [packetDensity_formula,add_sub_cancel_left,sub_zero] using he.symm
    simpa only [add_zero] using hm.trans hh
  · let G : Space → ℝ := fun z => g (-y+z)
    have hG : ContDiff ℝ 2 G := hg.comp (contDiff_const.add contDiff_id)
    have hcG : HasCompactSupport G := hcg.comp_homeomorph (Homeomorph.addLeft (-y))
    have hsG : tsupport G ⊆ ball y S := by
      intro z hz
      have ht := hs (tsupport_translate_subset y hz)
      simpa only [mem_ball,dist_eq_norm,sub_zero,neg_add_eq_sub] using ht
    have ht := hw G hG hcG hsG
    rw [tfLaplacian_translate g (-y)] at ht
    have hj := integral_add_left_eq_self (μ := volume) (fun z => u z*Δ g (-y+z)) y
    simpa only [neg_add_cancel_left] using hj.trans ht

theorem weak_harmonic_packet_mean_local {u : Space → ℝ} {y : Space} {R S : ℝ}
    (hu : ContinuousOn u (closedBall y S)) (hR : 0 < R) (hRS : R < S)
    (hw : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ ball y S → (∫ x, u x*Δ g x) = 0) :
    (∫ x, packetDensity y R x*u x) = u y := by
  let f : C(closedBall y S,ℝ) := ⟨_,hu.domRestrict⟩
  obtain ⟨v,hv⟩ := f.exists_restrict_eq isClosed_closedBall
  have he (z : Space) (hz : z ∈ closedBall y S) : v z = u z :=
    congrArg (fun h : C(closedBall y S,ℝ) => h ⟨z,hz⟩) hv
  have hm := weak_harmonic_packet_mean v.continuous y hR hRS (fun g hg hcg hs => ?_)
  · rw [he y (mem_closedBall_self (hR.trans hRS).le)] at hm
    refine (integral_congr_ae (Eventually.of_forall fun x => ?_)).trans hm
    by_cases hx : packetDensity y R x = 0
    · simp only [hx,zero_mul]
    · rw [he x ((closedBall_subset_closedBall hRS.le) ((mem_closedBall).mpr (packetDensity_support y hR hx)))]
  · convert hw g hg hcg hs using 1
    apply integral_congr_ae
    exact Eventually.of_forall fun z => by
      by_cases hz : Δ g z = 0
      · simp only [hz,mul_zero]
      · change v z*Δ g z = u z*Δ g z
        rw [he z (ball_subset_closedBall (hs (tfLaplacian_support hg hz)))]

end CoulombAnalysis

end

end OAI
