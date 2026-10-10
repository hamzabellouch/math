import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLE.LoewnerCharts

namespace OAI

/-! All radii in a late prescribed batch are uniformly small. Hence every
marked point above a fixed height has a uniformly long initial radius clock. -/

noncomputable section
open Set Filter
open scoped Topology

namespace SLEExactGauge.Target

lemma entryRadius_le_batch_exp {κ : ℝ} (hκ : 0<κ) (W : WienerLaw) (e : Entry) :
    entryRadius κ W e ≤ Real.exp (-(e.1:ℝ)^2) := by
  unfold entryRadius
  apply Real.exp_le_exp.mpr
  have ha := internal_a_pos hκ
  have hnonneg : 0≤2*a κ*(entryPosition κ W e:ℝ)*((batchLevel κ W e.1:ℝ)+(e.1:ℝ)) := by
    positivity
  linarith

lemma radii_uniformly_small {κ : ℝ} (hκ : 0<κ) (W : WienerLaw)
    (δ : ℝ) (hδ : 0<δ) :
    ∃ N : ℕ, ∀ e : GaugeIndex κ W, N≤e.val.1 → radii κ W e<δ := by
  obtain ⟨N,hN⟩ := exists_nat_gt (max 1 (-Real.log δ))
  refine ⟨N,?_⟩
  intro e he
  have hNe : (N:ℝ)≤(e.val.1:ℝ) := Nat.cast_le.mpr he
  have hn1 : (1:ℝ)≤(e.val.1:ℝ) := (le_max_left _ _).trans (hN.le.trans hNe)
  have hlog : -Real.log δ < (e.val.1:ℝ) := (le_max_right _ _).trans_lt (hN.trans_le hNe)
  apply (entryRadius_le_batch_exp hκ W e.val).trans_lt
  rw [← Real.exp_log hδ]
  apply Real.exp_lt_exp.mpr
  nlinarith

lemma uniform_marked_radius_gap {κ : ℝ} (hκ : 0<κ) (W : WienerLaw)
    (η A L : ℝ) (hη : 0<η) (hA : 0<A) :
    ∃ N : ℕ, ∀ e : GaugeIndex κ W, N≤e.val.1 → ∀ z : ℂ, η≤2*z.im →
      L < Real.log ((2*z.im)/(A*radii κ W e)) := by
  obtain ⟨N,hN⟩ := radii_uniformly_small hκ W (η/(A*Real.exp L)) (by positivity)
  refine ⟨N,?_⟩
  intro e he z hz
  have hr := radii_pos κ W e
  have hsmall := (lt_div_iff₀ (mul_pos hA (Real.exp_pos L))).mp (hN e he)
  apply (Real.lt_log_iff_exp_lt (div_pos (hη.trans_le hz) (mul_pos hA hr))).mpr
  apply (lt_div_iff₀ (mul_pos hA hr)).mpr
  nlinarith

end SLEExactGauge.Target

end

end OAI
