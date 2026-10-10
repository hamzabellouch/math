import OAI.NumberTheory.TotientAsymptotic.StructuralInput
import OAI.NumberTheory.TotientAsymptotic.Phase

namespace OAI

/-!
The comparison of the exact Ford band centers with the phase-dependent
centers in the manuscript, equation `alpha-comparison`.  The ratio is
independent of the retained prime index, so its convergence gives a
uniform comparison over all indices below `m`.
-/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

def bandCenterRatio (x : ℝ) : ℝ := Real.log (B x) / (lam * m x)

lemma rho_pow_eq_exp (j : ℕ) : rho^j = Real.exp (-lam * j) := by
  have hlog : Real.log rho = -lam := by
    simp only [lam, one_div, Real.log_inv, neg_neg]
  rw [mul_comm, ← hlog, Real.exp_nat_mul, Real.exp_log rho_pos]

lemma alpha_theta_eq {x : ℝ} (hB : 1 < B x) :
    alpha (theta x) = lam * (B x / Real.log (B x)) * rho^(m x) := by
  have hlog : 0 < Real.log (B x) := Real.log_pos hB
  have he : lam * theta x =
      (Real.log (B x) - Real.log (Real.log (B x))) - lam * m x := by
    unfold theta psi
    field_simp [lam_pos.ne']
  rw [alpha, he, Real.exp_sub, Real.exp_sub,
    Real.exp_log (zero_lt_one.trans hB), Real.exp_log hlog, rho_pow_eq_exp]
  rw [neg_mul, Real.exp_neg]
  ring

lemma bandScale_pos {x : ℝ} {i : ℕ} (hi : i < m x) : 0 < bandScale x i := by
  unfold bandScale
  exact mul_pos (mul_pos (alpha_pos _) (Nat.cast_pos.mpr (Nat.sub_pos_of_lt hi)))
    (inv_pos.mpr (pow_pos rho_pos _))

lemma fordBandScale_eq_ratio_mul {x : ℝ} {i : ℕ}
    (hB : 1 < B x) (hi : i < m x) :
    fordBandScale x i = bandCenterRatio x * bandScale x i := by
  have hm : (m x : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hl : Real.log (B x) ≠ 0 := (Real.log_pos hB).ne'
  have hpow : rho^(m x) = rho^(m x-i) * rho^i := by
    rw [← pow_add, Nat.sub_add_cancel hi.le]
  unfold fordBandScale bandCenterRatio bandScale
  rw [alpha_theta_eq hB, Nat.cast_sub hi.le, hpow]
  field_simp [hm, hl, lam_pos.ne', rho_pos.ne']

lemma fordBandScale_div_bandScale {x : ℝ} {i : ℕ}
    (hB : 1 < B x) (hi : i < m x) :
    fordBandScale x i / bandScale x i = bandCenterRatio x := by
  rw [fordBandScale_eq_ratio_mul hB hi, mul_div_cancel_right₀ _ (bandScale_pos hi).ne']

lemma bandCenterRatio_eq_one_add {x : ℝ} (hm : 0 < m x) :
    bandCenterRatio x =
      1 + (lam * theta x + Real.log (Real.log (B x))) / (lam * m x) := by
  have hm' : (m x : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  unfold bandCenterRatio theta psi
  field_simp [hm', lam_pos.ne']
  ring

lemma B_tendsto : Tendsto B atTop atTop :=
  Real.tendsto_log_atTop.comp Real.tendsto_log_atTop

lemma m_tendsto : Tendsto m atTop atTop :=
  tendsto_nat_floor_atTop.comp (psi_tendsto.comp B_tendsto)

lemma bandCenterRatio_tendsto : Tendsto bandCenterRatio atTop (nhds 1) := by
  have hlogB : Tendsto (fun x => Real.log (B x)) atTop atTop :=
    Real.tendsto_log_atTop.comp B_tendsto
  have hsmall : Tendsto (fun x => Real.log (Real.log (B x)) / Real.log (B x))
      atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hlogB
  have hpsi : Tendsto (fun x => psi (B x) / Real.log (B x))
      atTop (nhds (1 / lam)) := by
    have hh : Tendsto
        (fun x => (1 - Real.log (Real.log (B x)) / Real.log (B x)) / lam)
        atTop (nhds (1 / lam)) := by
      simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub hsmall).div_const lam
    apply hh.congr'
    filter_upwards [hlogB.eventually (eventually_gt_atTop (0 : ℝ))] with x hx
    unfold psi
    field_simp [hx.ne', lam_pos.ne']
  have hfloor : Tendsto (fun x => (m x : ℝ) / psi (B x)) atTop (nhds 1) :=
    tendsto_nat_floor_div_atTop.comp (psi_tendsto.comp B_tendsto)
  have hmratio : Tendsto (fun x => (m x : ℝ) / Real.log (B x))
      atTop (nhds (1 / lam)) := by
    have hh := hfloor.mul hpsi
    simp only [one_mul] at hh
    apply hh.congr'
    filter_upwards [(psi_tendsto.comp B_tendsto).eventually
      (eventually_gt_atTop (0 : ℝ))] with x hx
    change 0 < psi (B x) at hx
    field_simp [hx.ne']
  have hlm : Tendsto (fun x => lam * ((m x : ℝ) / Real.log (B x)))
      atTop (nhds 1) := by
    simpa only [mul_one_div_cancel lam_pos.ne'] using hmratio.const_mul lam
  have hh := hlm.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  change Tendsto (fun x => Real.log (B x) / (lam * m x)) atTop (nhds 1)
  simpa only [inv_one, mul_inv_rev, inv_div, inv_inv, div_eq_mul_inv,
    mul_comm, mul_left_comm, mul_assoc] using hh

/-- The error bound is simultaneous over every retained index. -/
theorem fordBandScale_uniform_comparison {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ i : ℕ, i < m x →
      |fordBandScale x i / bandScale x i - 1| < ε := by
  filter_upwards [B_tendsto.eventually (eventually_gt_atTop (1 : ℝ)),
    Metric.tendsto_nhds.mp bandCenterRatio_tendsto ε hε] with x hB hx
  intro i hi
  rw [fordBandScale_div_bandScale hB hi]
  simpa only [Real.dist_eq] using hx

/-- Ford's four-percent bands lie in the model's ten-percent bands for
all sufficiently large endpoints, uniformly over all retained indices. -/
theorem fordBands_imply_modelBands :
    ∀ᶠ x : ℝ in atTop, ∀ i : ℕ, i < m x → ∀ n : ℕ,
      fordBandCondition x (1/25) i n →
        (9/10 : ℝ) * bandScale x i ≤ primeDoubleLog n i ∧
          primeDoubleLog n i ≤ (11/10 : ℝ) * bandScale x i := by
  filter_upwards [B_tendsto.eventually (eventually_gt_atTop (1 : ℝ)),
    fordBandScale_uniform_comparison (ε := 1/25) (by norm_num)] with x hB hx
  intro i hi n hn
  have hscale := bandScale_pos hi
  have hford := fordBandScale_pos (zero_lt_one.trans hB) hi
  have hraw := (fordBandCondition_removes_clamp hford (by norm_num) hn).2
  have hmodel := abs_lt.mp (hx i hi)
  have hb := abs_le.mp hraw
  have hflow : (24/25 : ℝ) * bandScale x i < fordBandScale x i := by
    have hh := (lt_div_iff₀ hscale).mp (show (24/25 : ℝ) <
      fordBandScale x i / bandScale x i by linarith [hmodel.1])
    nlinarith
  have hfhigh : fordBandScale x i < (26/25 : ℝ) * bandScale x i := by
    have hh := (div_lt_iff₀ hscale).mp (show fordBandScale x i /
      bandScale x i < (26/25 : ℝ) by linarith [hmodel.2])
    nlinarith
  have hrawlow : (24/25 : ℝ) * fordBandScale x i ≤ primeDoubleLog n i := by
    have hh := (le_div_iff₀ hford).mp (show (24/25 : ℝ) ≤
      primeDoubleLog n i / fordBandScale x i by linarith [hb.1])
    nlinarith
  have hrawhigh : primeDoubleLog n i ≤ (26/25 : ℝ) * fordBandScale x i := by
    have hh := (div_le_iff₀ hford).mp (show primeDoubleLog n i /
      fordBandScale x i ≤ (26/25 : ℝ) by linarith [hb.2])
    nlinarith
  constructor <;> nlinarith

end TotientAsymptotic

end

end OAI
