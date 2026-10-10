import OAI.Analysis.CircleDomains.Topology.RoundDiskCoordinates

namespace OAI

/-!
# Bounded spherical round disks are Euclidean disks

The projective matrix action is converted to a norm inequality for its
inverse. Excluding infinity makes the leading quadratic coefficient
positive, so the completed-square formula gives a positive radius.
-/

open Set Function
open scoped ComplexConjugate

noncomputable section

namespace CircleDomainRigidity

theorem mobius_smul_mem_unit_disk_iff (M : Mobius) (z : ℂ) :
    M • (z : Sphere) ∈ ((↑) : ℂ → Sphere) '' Metric.closedBall 0 1 ↔
      ‖M 0 0 * z + M 0 1‖ ≤ ‖M 1 0 * z + M 1 1‖ := by
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 ≠ 0 := by
    simpa only [Matrix.det_fin_two] using M.det_ne_zero
  by_cases hden : M 1 0 * z + M 1 1 = 0
  · have hnum : M 0 0 * z + M 0 1 ≠ 0 := by
      intro hn
      apply hdet
      calc
        M 0 0 * M 1 1 - M 0 1 * M 1 0 =
            M 0 0 * (M 1 0 * z + M 1 1) - M 1 0 * (M 0 0 * z + M 0 1) := by ring
        _ = 0 := by rw [hden, hn]; ring
    simp only [OnePoint.smul_some_eq_ite, hden, ite_true, OnePoint.infty_notMem_image_coe,
      norm_zero, norm_le_zero_iff, hnum]
  · rw [OnePoint.smul_some_eq_ite, ite_eq_right hden,
      OnePoint.coe_injective.mem_set_image, Metric.mem_closedBall, dist_zero_right,
      norm_div, div_le_one (norm_pos_iff.mpr hden)]

theorem mobius_leading_normSq_pos (M : Mobius)
    (hinf : M • (OnePoint.infty : Sphere) ∉ ((↑) : ℂ → Sphere) '' Metric.closedBall 0 1) :
    0 < Complex.normSq (M 0 0) - Complex.normSq (M 1 0) := by
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 ≠ 0 := by
    simpa only [Matrix.det_fin_two] using M.det_ne_zero
  by_cases hc : M 1 0 = 0
  · have ha : M 0 0 ≠ 0 := by
      intro ha
      apply hdet
      simp only [ha, hc, zero_mul, mul_zero, sub_zero]
    rw [hc, Complex.normSq_zero, sub_zero]
    exact Complex.normSq_pos.mpr ha
  · rw [OnePoint.smul_infty_eq_ite, ite_eq_right hc,
      OnePoint.coe_injective.mem_set_image, Metric.mem_closedBall, dist_zero_right,
      norm_div, not_le] at hinf
    have hn : ‖M 1 0‖ < ‖M 0 0‖ := by
      simpa only [one_mul] using (lt_div_iff₀ (norm_pos_iff.mpr hc)).mp hinf
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg (M 1 0)]

theorem isRoundClosedDisk_eq_euclidean
    {K : Set Sphere} (hK : IsRoundClosedDisk K) (hinf : OnePoint.infty ∉ K) :
    ∃ (c : ℂ) (r : ℝ), 0 < r ∧ K = ((↑) : ℂ → Sphere) '' Metric.closedBall c r := by
  obtain ⟨M, rfl⟩ := hK
  let N : Mobius := M⁻¹
  let S : Set Sphere := ((↑) : ℂ → Sphere) '' Metric.closedBall 0 1
  have hmem (p : Sphere) : p ∈ (fun q : Sphere => M • q) '' S ↔ N • p ∈ S := by
    constructor
    · rintro ⟨q, hq, rfl⟩
      simpa only [N, inv_smul_smul] using hq
    · intro hp
      exact ⟨N • p, hp, smul_inv_smul M p⟩
  have hNinf : N • (OnePoint.infty : Sphere) ∉ S := by
    intro h
    exact hinf ((hmem _).mpr h)
  have hA := mobius_leading_normSq_pos N hNinf
  have hdet : N 0 0 * N 1 1 - N 0 1 * N 1 0 ≠ 0 := by
    simpa only [Matrix.det_fin_two] using N.det_ne_zero
  let c : ℂ := -(conj (N 0 0) * N 0 1 - conj (N 1 0) * N 1 1) /
    ((Complex.normSq (N 0 0) - Complex.normSq (N 1 0) : ℝ) : ℂ)
  let r : ℝ := ‖N 0 0 * N 1 1 - N 0 1 * N 1 0‖ /
    (Complex.normSq (N 0 0) - Complex.normSq (N 1 0))
  have hregion : {z : ℂ | ‖N 0 0 * z + N 0 1‖ ≤ ‖N 1 0 * z + N 1 1‖} =
      Metric.closedBall c r := fractional_norm_region_eq_closedBall _ _ _ _ hA
  refine ⟨c, r, div_pos (norm_pos_iff.mpr hdet) hA, ?_⟩
  ext p
  cases p using OnePoint.rec with
  | infty => exact iff_of_false hinf OnePoint.infty_notMem_image_coe
  | coe z =>
    rw [hmem, mobius_smul_mem_unit_disk_iff,
      OnePoint.coe_injective.mem_set_image, ← hregion]
    rfl

theorem isRoundClosedDisk_coe_closedBall (c : ℂ) {r : ℝ} (hr : 0 < r) :
    IsRoundClosedDisk (((↑) : ℂ → Sphere) '' Metric.closedBall c r) := by
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  refine ⟨affineMobius (r : ℂ) c hrc, ?_⟩
  rw [closedBall_eq_affine_image hr.le c, image_image, image_image]
  congr 1
  funext u
  rw [← affineSphere_eq_smul, affineSphere_coe]
  congr 1
  simp only [Complex.real_smul, mul_comm, add_comm]

theorem coe_closedBall_is_singleton_or_round (c : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    (∃ p : Sphere, ((↑) : ℂ → Sphere) '' Metric.closedBall c r = {p}) ∨
      IsRoundClosedDisk (((↑) : ℂ → Sphere) '' Metric.closedBall c r) := by
  rcases hr.eq_or_lt with he | hp
  · left
    refine ⟨(c : Sphere), ?_⟩
    rw [← he, Metric.closedBall_zero, image_singleton]
  · exact Or.inr (isRoundClosedDisk_coe_closedBall c hp)

end CircleDomainRigidity

end

end OAI
