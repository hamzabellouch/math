import OAI.NumberTheory.Jacobsthal.Renewal.DickmanFiniteDecay
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Order.LeftRight

namespace OAI

/-!
# The continuous Dickman distribution function

Continuity and endpoint behavior of the Dickman function determine its
continuous distribution function and the limiting order probabilities.
-/

namespace JointDickman

open Filter Erdos970.NumberTheoryLean
open scoped Topology

noncomputable def dickmanCDF (t : ℝ) : ℝ :=
  if t ≤ 0 then 0 else Dickman.rho (1 / t)

@[simp] theorem dickmanCDF_zero : dickmanCDF 0 = 0 := by simp [dickmanCDF]

theorem dickmanCDF_nonneg (t : ℝ) : 0 ≤ dickmanCDF t := by
  unfold dickmanCDF
  split_ifs
  · exact le_rfl
  · exact Dickman.rho_nonneg _

theorem dickmanCDF_le_one (t : ℝ) : dickmanCDF t ≤ 1 := by
  unfold dickmanCDF
  split_ifs
  · norm_num
  · exact DickmanFiniteDecay.rho_le_one _

theorem dickmanCDF_eq_one {t : ℝ} (ht : 1 ≤ t) : dickmanCDF t = 1 := by
  rw [dickmanCDF, ite_eq_right (by linarith)]
  apply Dickman.rho_initial
  exact (div_le_one (by linarith : 0 < t)).mpr ht

theorem dickmanCDF_monotone : Monotone dickmanCDF := by
  intro a b hab
  by_cases ha : a ≤ 0
  · simpa [dickmanCDF, ha] using dickmanCDF_nonneg b
  have ha' : 0 < a := lt_of_not_ge ha
  have hb : 0 < b := ha'.trans_le hab
  simp only [dickmanCDF, ite_eq_right ha, ite_eq_right (not_le.mpr hb)]
  exact Dickman.rho_antitone (one_div_le_one_div_of_le ha' hab)

theorem dickmanCDF_continuousAt_zero : ContinuousAt dickmanCDF 0 := by
  have hl : Tendsto dickmanCDF (𝓝[≤] (0 : ℝ)) (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : t ≤ 0 := ht
    simp [dickmanCDF, ht']
  have hr : Tendsto dickmanCDF (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := DickmanDecay.rho_tendsto_zero.comp
      (tendsto_inv_nhdsGT_zero : Tendsto (fun t : ℝ => t⁻¹) (𝓝[>] 0) atTop)
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : 0 < t := ht
    simp [dickmanCDF, not_le.mpr ht', one_div]
  have h := hl.sup hr
  rw [nhdsLE_sup_nhdsGT] at h
  simpa [ContinuousAt] using h

theorem dickmanCDF_continuous : Continuous dickmanCDF := by
  apply continuous_iff_continuousAt.mpr
  intro t
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · have heq : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝 t] dickmanCDF := by
      filter_upwards [eventually_lt_nhds ht] with x hx
      simp [dickmanCDF, hx.le]
    have h : Tendsto dickmanCDF (𝓝 t) (𝓝 0) := tendsto_const_nhds.congr' heq
    simpa [ContinuousAt, dickmanCDF, ht.le] using h
  · exact dickmanCDF_continuousAt_zero
  · have heq : (fun x : ℝ => Dickman.rho (1 / x)) =ᶠ[𝓝 t] dickmanCDF := by
      filter_upwards [eventually_gt_nhds ht] with x hx
      simp [dickmanCDF, not_le.mpr hx]
    have hcomp : ContinuousAt (fun x : ℝ => Dickman.rho (1 / x)) t :=
      Dickman.rho_continuous.continuousAt.comp
        (continuousAt_const.div continuousAt_id (ne_of_gt ht))
    have h := hcomp.tendsto.congr' heq
    simpa [ContinuousAt, dickmanCDF, not_le.mpr ht] using h

end JointDickman

end OAI
