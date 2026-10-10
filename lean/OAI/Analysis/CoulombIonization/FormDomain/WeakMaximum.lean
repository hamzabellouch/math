import Mathlib
import OAI.Analysis.CoulombIonization.Variational.CoulombTestCharge
import OAI.Analysis.CoulombIonization.Variational.NewtonComparisonTest

namespace OAI

noncomputable section

namespace CoulombAnalysis

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric Laplacian
open scoped BigOperators ContDiff Topology

open CoulombAtom

lemma newtonComparisonTest_pairing {r R : ℝ} (hr : 0 < r) (hR : 0 < R)
    {u : Space → ℝ} (hu : Continuous u) :
    (∫ x, u x*Δ (newtonComparisonTest r R) x) =
      4*Real.pi*((∫ x, packetDensity 0 R x*u x)-(∫ x, packetDensity 0 r x*u x)) := by
  have hi (a : ℝ) (ha : 0 < a) : Integrable (fun x => packetDensity 0 a x*u x) :=
    ((packetDensity_continuous 0 a).mul hu).integrable_of_hasCompactSupport
      (packetDensity_compact 0 ha).mul_right
  rw [newtonComparisonTest_laplacian hr hR]
  calc
    _ = ∫ x, 4*Real.pi*(packetDensity 0 R x*u x-packetDensity 0 r x*u x) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun _ => by ring
    _ = _ := by rw [integral_const_mul,integral_sub (hi R hR) (hi r hr)]

theorem weak_laplacian_no_positive_at_max {u : Space → ℝ} (hu : Continuous u)
    {S c : ℝ} (hS : 0 < S) (hc : 0 < c)
    (hmax : ∀ x ∈ ball (0 : Space) S, u x ≤ u 0)
    (hw : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ ball 0 S → (∀ x, 0 ≤ g x) →
      c*(∫ x, g x) ≤ ∫ x, u x*Δ g x) : False := by
  let R := S/2
  have hR : 0 < R := half_pos hS
  have hRS : R < S := half_lt_self hS
  let r : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have hr (n : ℕ) : 0 < r n := by dsimp [r]; positivity
  have hr0 : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hpot := tfPotential_continuous (packetDensity_integrable 0 hR) (packetDensity_memLp 0 hR)
  obtain ⟨z,hz,hMz⟩ := (isCompact_closedBall (0 : Space) R).exists_isMaxOn
    (show (closedBall (0 : Space) R).Nonempty from ⟨0,by simp [hR.le]⟩) hpot.continuousOn
  let M := tfPotential (packetDensity 0 R) z
  have hM0 : 0 ≤ M := tfPotential_nonneg (Eventually.of_forall (packetDensity_nonneg 0 R)) z
  have hev : ∀ᶠ n in atTop, c*(∫ x, newtonComparisonTest (r n) R x) ≤
      ∫ x, u x*Δ (newtonComparisonTest (r n) R) x := by
    filter_upwards [hr0.eventually (gt_mem_nhds hR),
      hr0.eventually (gt_mem_nhds (by positivity : 0 < 1/(M+1)))] with n hn hnM
    apply hw _ (newtonComparisonTest_smooth (hr n) hR) (newtonComparisonTest_compact (hr n) hR)
    · exact (newtonComparisonTest_tsupport (hr n) hR hn.le).trans
        (closedBall_subset_ball hRS)
    · apply newtonComparisonTest_nonneg (hr n) hR hn.le (fun x hx => hMz hx)
      apply (le_div_iff₀ (hr n)).mpr
      have hh := (lt_div_iff₀ (by positivity : 0 < M+1)).mp hnM
      nlinarith [hr n]
  have hm0 : Tendsto (fun n => packetSecondMoment (r n)) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => packetSecondMoment_nonneg (r n))
      (fun n => packetSecondMoment_le (hr n))
    convert hr0.pow 2 using 1; norm_num
  have hgint : Tendsto (fun n => ∫ x, newtonComparisonTest (r n) R x) atTop
      (𝓝 ((4*Real.pi/6)*packetSecondMoment R)) := by
    have hh := (((tendsto_const_nhds (x := packetSecondMoment R)).sub hm0).const_mul (4*Real.pi/6))
    simp only [sub_zero] at hh
    apply hh.congr
    intro n
    have he := newtonComparisonTest_integral (hr n) hR
    linarith
  have hravg : Tendsto (fun n => ∫ x, packetDensity 0 (r n) x*u x) atTop (𝓝 (u 0)) :=
    shrinking_density_test_limit (fun n => packetDensity_continuous 0 (r n))
      (fun n => packetDensity_compact 0 (hr n)) (fun n => packetDensity_nonneg 0 (r n))
      (fun n => packetDensity_mass 0 (hr n))
      (fun n x hx => by simpa only [sub_zero] using packetDensity_support 0 (hr n) hx) hr0 hu
  have hgpair : Tendsto (fun n => ∫ x, u x*Δ (newtonComparisonTest (r n) R) x) atTop
      (𝓝 (4*Real.pi*((∫ x, packetDensity 0 R x*u x)-u 0))) := by
    have hh := ((tendsto_const_nhds (x := ∫ x, packetDensity 0 R x*u x)).sub hravg).const_mul (4*Real.pi)
    exact hh.congr (fun n => (newtonComparisonTest_pairing (hr n) hR hu).symm)
  have havg : (∫ x, packetDensity 0 R x*u x) ≤ u 0 := by
    calc
      _ ≤ ∫ x, packetDensity 0 R x*u 0 := by
        apply integral_mono
          (((packetDensity_continuous 0 R).mul hu).integrable_of_hasCompactSupport
            (packetDensity_compact 0 hR).mul_right)
          ((packetDensity_integrable 0 hR).mul_const _)
        intro x
        by_cases hx : packetDensity 0 R x = 0
        · simp [hx]
        · apply mul_le_mul_of_nonneg_left (hmax x _) (packetDensity_nonneg 0 R x)
          have hn := packetDensity_support 0 hR hx
          simpa only [mem_ball,dist_zero_right] using
            (show ‖x‖ < S from (by simpa only [sub_zero] using hn : ‖x‖ ≤ R).trans_lt hRS)
      _ = u 0 := by rw [integral_mul_const,packetDensity_mass 0 hR,one_mul]
  have hle := le_of_tendsto_of_tendsto (hgint.const_mul c) hgpair hev
  have hp : 0 < c*((4*Real.pi/6)*packetSecondMoment R) :=
    mul_pos hc (mul_pos (by positivity) (packetSecondMoment_pos hR))
  have hn : 4*Real.pi*((∫ x, packetDensity 0 R x*u x)-u 0) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr havg)
  exact (not_le_of_gt hp) (hle.trans hn)

open MeasureTheory Filter Set Metric Laplacian
open scoped BigOperators ContDiff Topology

open CoulombAtom

lemma tsupport_translate_subset {g : Space → ℝ} (y : Space) :
    tsupport (fun z => g (-y+z)) ⊆ (fun z => -y+z) ⁻¹' tsupport g := by
  apply closure_minimal _ (isClosed_closure.preimage (continuous_const.add continuous_id))
  intro z hz
  exact subset_tsupport g hz

lemma weak_laplacian_no_positive_at_max_center {u : Space → ℝ} (hu : Continuous u)
    {y : Space} {S c : ℝ} (hS : 0 < S) (hc : 0 < c)
    (hmax : ∀ x ∈ ball y S, u x ≤ u y)
    (hw : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ ball y S → (∀ x, 0 ≤ g x) →
      c*(∫ x, g x) ≤ ∫ x, u x*Δ g x) : False := by
  apply weak_laplacian_no_positive_at_max (u := fun x => u (y+x))
    (hu.comp (continuous_const.add continuous_id)) hS hc
  · intro x hx
    simpa only [add_zero] using hmax (y+x) (by
      simpa only [mem_ball,dist_eq_norm,add_sub_cancel_left,sub_zero] using hx)
  · intro g hg hcg hs hn
    let G : Space → ℝ := fun z => g (-y+z)
    have hG : ContDiff ℝ 2 G := hg.comp (contDiff_const.add contDiff_id)
    have hcG : HasCompactSupport G := hcg.comp_homeomorph (Homeomorph.addLeft (-y))
    have hsG : tsupport G ⊆ ball y S := by
      intro z hz
      have hh := hs (tsupport_translate_subset y hz)
      simpa only [mem_ball,dist_eq_norm,sub_zero,neg_add_eq_sub] using hh
    have hh := hw G hG hcG hsG (fun _ => hn _)
    have hi : (∫ x, G x) = ∫ x, g x := integral_add_left_eq_self (μ := volume) g (-y)
    rw [hi,tfLaplacian_translate g (-y)] at hh
    have hj := integral_add_left_eq_self (μ := volume) (fun z => u z*Δ g (-y+z)) y
    simpa only [neg_add_cancel_left] using hh.trans_eq hj.symm

theorem weak_laplacian_no_positive_at_max_local {u : Space → ℝ}
    {y : Space} {S c : ℝ} (hu : ContinuousOn u (closedBall y S))
    (hS : 0 < S) (hc : 0 < c)
    (hmax : ∀ x ∈ ball y S, u x ≤ u y)
    (hw : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ ball y S → (∀ x, 0 ≤ g x) →
      c*(∫ x, g x) ≤ ∫ x, u x*Δ g x) : False := by
  let f : C(closedBall y S,ℝ) := ⟨_,hu.domRestrict⟩
  obtain ⟨v,hv⟩ := f.exists_restrict_eq isClosed_closedBall
  have he (z : Space) (hz : z ∈ closedBall y S) : v z = u z :=
    congrArg (fun h : C(closedBall y S,ℝ) => h ⟨z,hz⟩) hv
  apply weak_laplacian_no_positive_at_max_center v.continuous hS hc
  · intro z hz
    rw [he z (ball_subset_closedBall hz),he y (mem_closedBall_self hS.le)]
    exact hmax z hz
  · intro g hg hcg hs hn
    convert hw g hg hcg hs hn using 1
    apply integral_congr_ae
    exact Eventually.of_forall fun z => by
      by_cases hz : Δ g z = 0
      · simp only [hz,mul_zero]
      · change v z * Δ g z = u z * Δ g z
        rw [he z (ball_subset_closedBall (hs (tfLaplacian_support hg hz)))]

end CoulombAnalysis

end

end OAI
