import OAI.Analysis.KadisonKastler.InfinitesimalExponentiation
import OAI.Analysis.KadisonKastler.NormalizerDefect
import OAI.Analysis.KadisonKastler.UnitaryLogarithmBound
import OAI.Analysis.KadisonKastler.NormalizerPathBarrier

namespace OAI

/-! # The local quadratic estimate for approximate normalizers -/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem exists_small_log_of_separate_translate
    (M : VonNeumannAlgebra H) (v : unitary (H →L[ℂ] H)) {r : ℝ}
    (hr : Metric.infDist (v : H →L[ℂ] H) (separateUnitaryProducts M) < r)
    (hr2 : r < 2) :
    ∃ p : unitary (H →L[ℂ] H), (p : H →L[ℂ] H) ∈ separateUnitaryProducts M ∧
      ∃ h : selfAdjoint (H →L[ℂ] H), selfAdjoint.expUnitary h = star p * v ∧
        ‖(h : H →L[ℂ] H)‖ ≤ 2 * r := by
  obtain ⟨p0, hp0, hnear⟩ := (Metric.infDist_lt_iff
    (show (separateUnitaryProducts M).Nonempty from
      ⟨1, one_mem_separateUnitaryProducts M⟩)).mp hr
  obtain ⟨a, b, ha, hb, rfl⟩ := hp0
  let p : unitary (H →L[ℂ] H) := a * b
  have hp : (p : H →L[ℂ] H) ∈ separateUnitaryProducts M := ⟨a, b, ha, hb, rfl⟩
  let w : unitary (H →L[ℂ] H) := star p * v
  have hwn : ‖(w : H →L[ℂ] H) - 1‖ < r := by
    have heq : (w : H →L[ℂ] H) - 1 = star (p : H →L[ℂ] H) *
        ((v : H →L[ℂ] H) - p) := by
      change star (p : H →L[ℂ] H) * v - 1 = _
      rw [mul_sub, Unitary.star_mul_self_of_mem p.property]
    rw [heq, ← Unitary.coe_star, CStarRing.norm_coe_unitary_mul]
    simpa only [dist_eq_norm, p] using hnear
  obtain ⟨h, hlog, hnorm⟩ := exists_small_selfAdjoint_log w (hwn.trans hr2)
  exact ⟨p, hp, h, hlog, hnorm.trans (by linarith)⟩

private theorem conjugation_approximation_separate_translate
    (M : VonNeumannAlgebra H) (v p : unitary (H →L[ℂ] H))
    (hp : (p : H →L[ℂ] H) ∈ separateUnitaryProducts M) {e : ℝ}
    (he : ∀ x ∈ unitBall M, Metric.infDist (unitaryConj (H := H) v x)
      (M : Set (H →L[ℂ] H)) ≤ e) :
    ∀ x ∈ unitBall M, Metric.infDist (unitaryConj (H := H) (star p * v) x)
      (M : Set (H →L[ℂ] H)) ≤ e := by
  intro x hx
  rw [unitaryConj_mul, infDist_unitaryConj_normalizer M (star p)
    (conjugates_of_mem_separateUnitaryProducts M hp).symm]
  exact he x hx

private theorem normalizer_distance_bound_with_slack
    (M : VonNeumannAlgebra H) {K : ℝ} (hK : 0 ≤ K)
    (hlinear : ∀ h : selfAdjoint (H →L[ℂ] H),
      Metric.infDist (h : H →L[ℂ] H) (selfAdjointAlgebraCommutantSum M) ≤
        K * commutatorRangeError M (h : H →L[ℂ] H))
    (v : unitary (H →L[ℂ] H)) {e r : ℝ}
    (he : ∀ x ∈ unitBall M, Metric.infDist (unitaryConj (H := H) v x)
      (M : Set (H →L[ℂ] H)) ≤ e)
    (hr : Metric.infDist (v : H →L[ℂ] H) (separateUnitaryProducts M) < r)
    (hr2 : r < 2) :
    Metric.infDist (v : H →L[ℂ] H) (separateUnitaryProducts M) ≤
      K * (e + 16 * r ^ 2) := by
  obtain ⟨p, hp, h, hlog, hn⟩ := exists_small_log_of_separate_translate M v hr hr2
  have heh : ∀ x ∈ unitBall M,
      Metric.infDist (unitaryConj (H := H) (selfAdjoint.expUnitary h) x)
        (M : Set (H →L[ℂ] H)) ≤ e := by
    rw [hlog]
    exact conjugation_approximation_separate_translate M v p hp he
  have hdef := commutatorRangeError_le_of_exp_approx M h heh
  have hdist := infDist_expUnitary_le_infDist_selfAdjointSum M h
  rw [hlog] at hdist
  have heqdist := infDist_separateUnitaryProducts_left M p hp (v : H →L[ℂ] H)
  change Metric.infDist (star (p : H →L[ℂ] H) * (v : H →L[ℂ] H))
    (separateUnitaryProducts M) ≤ _ at hdist
  rw [heqdist] at hdist
  calc
    _ ≤ K * commutatorRangeError M (h : H →L[ℂ] H) := hdist.trans (hlinear h)
    _ ≤ K * (e + 4 * ‖(h : H →L[ℂ] H)‖ ^ 2) := mul_le_mul_of_nonneg_left hdef hK
    _ ≤ K * (e + 16 * r ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hK
      have hs := mul_self_le_mul_self (norm_nonneg (h : H →L[ℂ] H)) hn
      nlinarith

theorem normalizer_distance_quadratic
    (M : VonNeumannAlgebra H) {K : ℝ} (hK : 0 ≤ K)
    (hlinear : ∀ h : selfAdjoint (H →L[ℂ] H),
      Metric.infDist (h : H →L[ℂ] H) (selfAdjointAlgebraCommutantSum M) ≤
        K * commutatorRangeError M (h : H →L[ℂ] H))
    (v : unitary (H →L[ℂ] H)) {e : ℝ}
    (he : ∀ x ∈ unitBall M, Metric.infDist (unitaryConj (H := H) v x)
      (M : Set (H →L[ℂ] H)) ≤ e)
    (hsmall : Metric.infDist (v : H →L[ℂ] H) (separateUnitaryProducts M) < 1) :
    Metric.infDist (v : H →L[ℂ] H) (separateUnitaryProducts M) ≤
      K * e + 16 * K * (Metric.infDist (v : H →L[ℂ] H) (separateUnitaryProducts M)) ^ 2 := by
  let d := Metric.infDist (v : H →L[ℂ] H) (separateUnitaryProducts M)
  let r (n : ℕ) := d + (1 - d) * (1 / (n + 1 : ℝ))
  have hd : 0 ≤ d := Metric.infDist_nonneg
  have hdr : d < 1 := hsmall
  have hr (n : ℕ) : d < r n := by
    dsimp [r]
    exact lt_add_of_pos_right d (mul_pos (sub_pos.mpr hdr) (by positivity))
  have hr2 (n : ℕ) : r n < 2 := by
    have hn : 1 / (n + 1 : ℝ) ≤ 1 := by
      apply (div_le_one (by positivity)).mpr
      norm_num
    dsimp [r]
    have hmul := mul_le_mul_of_nonneg_left hn (sub_nonneg.mpr hdr.le)
    linarith
  have hbound (n : ℕ) : d ≤ K * (e + 16 * r n ^ 2) :=
    normalizer_distance_bound_with_slack M hK hlinear v he (hr n) (hr2 n)
  have hrt : Tendsto r atTop (𝓝 d) := by
    have ht : Tendsto (fun n : ℕ => d + (1 - d) * (1 / (n + 1 : ℝ))) atTop
        (𝓝 (d + (1 - d) * 0)) :=
      tendsto_const_nhds.add
        (tendsto_const_nhds.mul tendsto_one_div_add_atTop_nhds_zero_nat)
    simpa only [mul_zero, add_zero] using ht
  have ht : Tendsto (fun n : ℕ => K * (e + 16 * r n ^ 2)) atTop
      (𝓝 (K * (e + 16 * d ^ 2))) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.add
      (tendsto_const_nhds.mul (hrt.pow 2)))
  have hb := le_of_tendsto_of_tendsto' tendsto_const_nhds ht hbound
  convert hb using 1; ring

end

end KadisonKastler

end OAI
