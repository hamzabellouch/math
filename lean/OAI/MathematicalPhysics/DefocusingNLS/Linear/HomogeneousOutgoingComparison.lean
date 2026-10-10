import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousOutgoingEstimates
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousDefectComparison
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousEulerPhysical

namespace OAI

/-! # The high radial derivative detects the transverse outgoing defect

The exact Euler recurrence separates its velocity row from the outgoing
remainder. Dividing by the physical derivative scaling gives the power
comparison used with radial square integrability.
-/

open Set Filter Topology
open scoped ContDiff

namespace DefocusingNLS

local notation "V" => ℂ × ℂ
local notation "End" => V →L[ℂ] V

theorem homogeneousEulerRows_defect_identity
    (B C : ℝ → End) (u v du dv F G : ℝ → V) (L : ℝ)
    (hB : ContDiffOn ℝ ∞ B (Ioi L)) (hC : ContDiffOn ℝ ∞ C (Ioi L))
    (hu : ∀ t, L < t → HasDerivAt u (du t) t)
    (hv : ∀ t, L < t → HasDerivAt v (dv t) t)
    (hdu : ∀ t, L < t → HasDerivAt du (-B t (du t) - C t (u t)) t)
    (hdv : ∀ t, L < t → HasDerivAt dv (-B t (dv t) - C t (v t)) t)
    (hF : ∀ t, L < t → HasDerivAt F (G t) t)
    (hG : ∀ t, L < t → HasDerivAt G (-B t (G t) - C t (F t)) t)
    (n : ℕ) (t : ℝ) (ht : L < t) (hd : spectralValueDet (u t) (v t) ≠ 0) :
    homogeneousEulerDeriv F n t =
      (homogeneousEulerRows B C n).2 t
        (G t - spectralRobinOperator (u t) (v t) (du t) (dv t) (F t)) +
      (spectralTwoColumns (homogeneousEulerDeriv u n t)
        (homogeneousEulerDeriv v n t) * spectralValueInverse (u t) (v t)) (F t) := by
  rw [homogeneousEulerRows_identity B C F G L hB hC hF hG n t ht,
    ← homogeneousEulerRows_outgoing_remainder B C u v du dv L hB hC
      hu hv hdu hdv n t ht hd]
  simp only [add_apply, mul_apply_eq_comp, map_sub]
  abel

theorem homogeneousLogRow_norm_comparison
    (U W H : V) (T R : End) (r c K M : ℝ) (n : ℕ)
    (hr : 0 < r) (hK : 0 ≤ K)
    (hrow : c * r ^ (2 * n) * ‖r • W‖ ≤ ‖T (r • W)‖)
    (hidentity : r ^ (n + 1) • H = T (r • W) + R U)
    (hR : ‖R‖ ≤ K) (hU : ‖U‖ ≤ M) :
    c * r ^ n * ‖W‖ ≤ ‖H‖ + K * M / r ^ (n + 1) := by
  have hRnorm : ‖R U‖ ≤ K * M :=
    (ContinuousLinearMap.le_opNorm R U).trans
      (mul_le_mul hR hU (norm_nonneg _) hK)
  have htri : ‖T (r • W)‖ ≤ r ^ (n + 1) * ‖H‖ + K * M := by
    calc
      _ = ‖r ^ (n + 1) • H - R U‖ := by rw [hidentity, add_sub_cancel_right]
      _ ≤ ‖r ^ (n + 1) • H‖ + ‖R U‖ := norm_sub_le _ _
      _ ≤ r ^ (n + 1) * ‖H‖ + K * M := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos hr _)]
        exact add_le_add le_rfl hRnorm
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr] at hrow
  have hp : r ^ (2 * n) * r = r ^ n * r ^ (n + 1) := by
    rw [two_mul, pow_add, pow_succ]
    ring
  apply (mul_le_mul_iff_left₀ (pow_pos hr (n + 1))).mp
  calc
    (c * r ^ n * ‖W‖) * r ^ (n + 1) = c * (r ^ n * r ^ (n + 1)) * ‖W‖ := by ring
    _ = c * r ^ (2 * n) * (r * ‖W‖) := by rw [← hp]; ring
    _ ≤ r ^ (n + 1) * ‖H‖ + K * M := hrow.trans htri
    _ = (‖H‖ + K * M / r ^ (n + 1)) * r ^ (n + 1) := by
      field_simp [hr.ne']

theorem homogeneousLogRow_energy_comparison
    (U W H : V) (T R : End) (r c K M : ℝ) (n : ℕ)
    (hr : 0 < r) (hc : 0 < c) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hrow : c * r ^ (2 * n) * ‖r • W‖ ≤ ‖T (r • W)‖)
    (hidentity : r ^ (n + 1) • H = T (r • W) + R U)
    (hR : ‖R‖ ≤ K) (hU : ‖U‖ ≤ M) :
    r ^ (2 * (n : ℝ)) * homogeneousPairEnergy W ≤
      (4 / c ^ 2) * homogeneousPairEnergy H +
        (4 / c ^ 2) * (K * M) ^ 2 * r ^ (-2 * ((n + 1 : ℕ) : ℝ)) := by
  have he := homogeneousPair_energy_control W H (r ^ n)
    (K * M / r ^ (n + 1)) c (pow_nonneg hr.le _) (by positivity) hc
    (homogeneousLogRow_norm_comparison U W H T R r c K M n hr hK
      hrow hidentity hR hU)
  have hp : r ^ (2 * (n : ℝ)) = (r ^ n) ^ 2 := by
    rw [mul_comm (2 : ℝ), Real.rpow_mul hr.le, Real.rpow_ofNat, Real.rpow_natCast]
  have hq : r ^ (-2 * ((n + 1 : ℕ) : ℝ)) = ((r ^ (n + 1))⁻¹) ^ 2 := by
    rw [show -2 * ((n + 1 : ℕ) : ℝ) = (-((n + 1 : ℕ) : ℝ)) * 2 by ring,
      Real.rpow_mul hr.le, Real.rpow_ofNat, Real.rpow_neg hr.le, Real.rpow_natCast]
  rw [hp, hq]
  convert he using 1
  simp only [div_eq_mul_inv, mul_pow]
  ring

end DefocusingNLS

end OAI
