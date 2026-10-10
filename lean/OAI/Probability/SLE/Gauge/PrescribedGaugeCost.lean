import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLE.Gauge.DenseCandidateCover

namespace OAI

/-! The prescribed quadratic envelope directly pays for enlarged candidate
balls and for final cells. Its infinite-diameter convention gives the same
Hausdorff outer measure, since the defining limit uses small covers. -/
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Target

lemma hausdorff_eq_hausdorffGauge (h : ℝ → ℝ) :
    Target.hausdorff h = (hausdorffGauge h).toOuterMeasure := by
  rw [hausdorffGauge,Measure.mkMetric_toOuterMeasure]
  unfold Target.hausdorff
  apply le_antisymm <;> apply OuterMeasure.mkMetric_mono
  · filter_upwards [gt_mem_nhds (show (0:ℝ≥0∞)<∞ from ENNReal.zero_lt_top)] with r hr
    simp only [ne_of_lt hr,ite_false,extendedGauge,le_refl]
  · filter_upwards [] with r
    unfold extendedGauge
    split_ifs <;> simp

lemma gauge_le_entry (κ : ℝ) (W : WienerLaw) (e : Entry)
    (he : ValidEntry κ W e) (r : ℝ) : gauge κ W r ≤ entryCost κ W e r := by
  rw [gauge_eq_full]
  exact QuadraticEnvelope.full_le_profile
    (fun i => (weights_pos κ W i).le) (radii_pos κ W) ⟨e,he⟩ r

lemma gauge_scaled_entry_le (κ : ℝ) (W : WienerLaw) (e : Entry)
    (he : ValidEntry κ W e) (C : ℝ) :
    gauge κ W (C*entryRadius κ W e) ≤
      max 1 (C^2)*entryValue e*(entryRadius κ W e)^d κ := by
  have hr : entryRadius κ W e ≠ 0 := (Real.exp_pos _).ne'
  convert gauge_le_entry κ W e he (C*entryRadius κ W e) using 1
  unfold entryCost
  rw [mul_div_cancel_right₀ _ hr]
  ring

lemma enlarged_candidate_gauge_cost {κ : ℝ} (W : WienerLaw)
    (hg : IsHausdorffGauge (gauge κ W)) (e : Entry) (he : ValidEntry κ W e)
    (z : ℂ) {C c : ℝ} (hC : 1≤C) (hc : 0<c) (ν : Measure ℂ)
    (hqualified : ENNReal.ofReal (c*entryValue e*(entryRadius κ W e)^d κ) ≤
      ν (closedBall z (C*entryRadius κ W e))) :
    extendedGauge (gauge κ W) (ediam (closedBall z (4*C*entryRadius κ W e))) ≤
      ENNReal.ofReal ((8*C)^2/c)*ν (closedBall z (C*entryRadius κ W e)) := by
  have hh : IsGauge (gauge κ W) := ⟨hg.1,hg.2.1,hg.2.2.1,hg.2.2.2⟩
  have hC0 : 0≤C := by linarith
  have hr := radii_pos κ W ⟨e,he⟩
  have hm : max 1 ((8*C)^2)=(8*C)^2 := by
    apply max_eq_right
    nlinarith
  have hbound := gauge_scaled_entry_le κ W e he (8*C)
  rw [hm] at hbound
  have hconst : 0≤(8*C)^2/c := div_nonneg (sq_nonneg _) hc.le
  calc
    _ ≤ ENNReal.ofReal (gauge κ W (2*(4*C*entryRadius κ W e))) :=
      extendedGauge_closedBall_le hh z (by positivity)
    _ = ENNReal.ofReal (gauge κ W ((8*C)*entryRadius κ W e)) := by congr 2; ring
    _ ≤ ENNReal.ofReal ((8*C)^2*entryValue e*(entryRadius κ W e)^d κ) :=
      ENNReal.ofReal_le_ofReal hbound
    _ = ENNReal.ofReal ((8*C)^2/c)*
        ENNReal.ofReal (c*entryValue e*(entryRadius κ W e)^d κ) := by
      rw [← ENNReal.ofReal_mul hconst]
      congr 1
      field_simp
    _ ≤ _ := mul_le_mul' le_rfl hqualified

lemma cleanup_cell_gauge_cost {κ : ℝ} (W : WienerLaw)
    (hg : IsHausdorffGauge (gauge κ W)) (n : ℕ) (hn : 1≤n) (z : ℂ) :
    extendedGauge (gauge κ W)
      (ediam (closedBall z (2*entryRadius κ W (n,none)))) ≤
      ENNReal.ofReal (16*(n:ℝ)*(entryRadius κ W (n,none))^d κ) := by
  have hh : IsGauge (gauge κ W) := ⟨hg.1,hg.2.1,hg.2.2.1,hg.2.2.2⟩
  have hr : 0<entryRadius κ W (n,none) := Real.exp_pos _
  calc
    _ ≤ ENNReal.ofReal (gauge κ W (2*(2*entryRadius κ W (n,none)))) :=
      extendedGauge_closedBall_le hh z (by positivity)
    _ = ENNReal.ofReal (gauge κ W (4*entryRadius κ W (n,none))) := by congr 2; ring
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      simpa only [show (max (1:ℝ) (4^2))=16 by norm_num,entryValue] using
        gauge_scaled_entry_le κ W (n,none) ⟨hn,trivial⟩ 4

end SLEExactGauge.Target

end

end OAI
