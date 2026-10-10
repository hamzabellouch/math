import OAI.NumberTheory.Catalan.Estimates.RealEnergyChebyshev
import OAI.NumberTheory.Catalan.Estimates.RealEnergyDiagonal
import OAI.NumberTheory.Catalan.Estimates.TwoAdicQuadratic

namespace OAI

noncomputable section

namespace InternalCatalan

section

open Set
open scoped ComplexConjugate

theorem energy_log_chord_lower (z : ℂ) (hz : ‖z‖ = 1) {r : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) 1) :
    Real.log (1 - r) ≤ Real.log ‖(1 : ℂ) - (r : ℂ) * z‖ := by
  have hn : ‖(r : ℂ) * z‖ = r := by
    rw [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr.1, hz, mul_one]
  have ht := norm_add_le ((1 : ℂ) - (r : ℂ) * z) ((r : ℂ) * z)
  rw [sub_add_cancel, norm_one, hn] at ht
  exact Real.log_le_log (sub_pos.mpr hr.2) (by linarith)

theorem realEnergyCosineKernel_lower {r u v : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) 1)
    (hu : u ∈ Icc (-1 : ℝ) 1) (hv : v ∈ Icc (-1 : ℝ) 1) :
    -Real.log 2 + 2 * Real.log (1 - r) ≤ realEnergyCosineKernel r u v := by
  have hn1 : ‖realEnergyCirclePoint u * realEnergyCirclePoint v‖ = 1 := by
    rw [Complex.norm_mul, realEnergyCirclePoint_norm hu, realEnergyCirclePoint_norm hv, one_mul]
  have hn2 : ‖realEnergyCirclePoint u * conj (realEnergyCirclePoint v)‖ = 1 := by
    rw [Complex.norm_mul, Complex.norm_conj,
      realEnergyCirclePoint_norm hu, realEnergyCirclePoint_norm hv, one_mul]
  have h1 := energy_log_chord_lower _ hn1 hr
  have h2 := energy_log_chord_lower _ hn2 hr
  unfold realEnergyCosineKernel
  linarith

theorem realEnergy_cosine_tau_diagonal_lower {e x : ℝ}
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) (hx : x ∈ Icc (-1 : ℝ) 1) :
    -Real.log 2 + 2 * Real.log (1 - realEnergyTau e ^ 2) ≤
      realEnergyCosineKernel (realEnergyTau e ^ 2) x x := by
  have ht := realEnergyTau_bounds he
  have ht2 : realEnergyTau e ^ 2 < 1 := by
    nlinarith [mul_pos ht.1 (sub_pos.mpr ht.2)]
  exact realEnergyCosineKernel_lower ⟨sq_pos_of_pos ht.1, ht2⟩ hx hx

theorem realEnergy_cosine_sigma_diagonal_lower {e s : ℝ}
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) (hs : s ∈ Ioo (0 : ℝ) 1) :
    -Real.log 2 + 2 * Real.log e + Real.log (1 - s) ≤
      realEnergyCosineKernel (realEnergySigma e s ^ 2) s s := by
  have ht := realEnergySigma_mem he hs
  have ht2 : realEnergySigma e s ^ 2 < 1 := by
    nlinarith [mul_pos ht.1 (sub_pos.mpr ht.2)]
  have hs' : s ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hs.1], hs.2.le⟩
  have hk := realEnergyCosineKernel_lower ⟨sq_pos_of_pos ht.1, ht2⟩ hs' hs'
  have hd := realEnergy_log_sigma_diagonal_ge he hs
  linarith

end

open Set
open scoped BigOperators

theorem realEnergy_tau_diagonal_sum {N : ℕ} (hN : 0 < N)
    {e k : ℝ} (he : e ∈ Ioo (0 : ℝ) (1 / 8)) (hk : 0 ≤ k)
    {x : Fin (n N) → ℝ} (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) :
    -(k / (2 * (n N : ℝ) ^ 2)) *
        (∑ i : Fin (n N), realEnergyCosineKernel (realEnergyTau e ^ 2) (x i) (x i)) ≤
      k * (Real.log 2 - 2 * Real.log (1 - realEnergyTau e ^ 2)) / (2 * (n N : ℝ)) := by
  have hn : (0 : ℝ) < n N := by
    have hnpos : 0 < n N := by unfold n; omega
    exact Nat.cast_pos.mpr hnpos
  have hb := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    realEnergy_cosine_tau_diagonal_lower he ⟨(hx i).1.le, (hx i).2.le⟩)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hb
  have hm := mul_le_mul_of_nonneg_left hb
    (show 0 ≤ k / (2 * (n N : ℝ) ^ 2) by positivity)
  have hc : k / (2 * (n N : ℝ) ^ 2) *
      ((n N : ℝ) * (-Real.log 2 + 2 * Real.log (1 - realEnergyTau e ^ 2))) =
      -(k * (Real.log 2 - 2 * Real.log (1 - realEnergyTau e ^ 2)) / (2 * (n N : ℝ))) := by
    field_simp [hn.ne']
    ring
  rw [hc] at hm
  linarith

theorem realEnergy_power_diagonal_sum {N : ℕ} (hN : 0 < N)
    {e : ℝ} (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    {x : Fin (n N) → ℝ} (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) :
    -(∑ i : Fin (n N), Real.log (1 - realEnergyRho e (x i) ^ 2 * x i ^ 2)) /
        (2 * (n N : ℝ) ^ 2) ≤
      -(∑ i : Fin (n N), Real.log (1 - x i)) / (2 * (n N : ℝ) ^ 2) +
        (Real.log 2 - Real.log e) / (2 * (n N : ℝ)) := by
  have hn : (0 : ℝ) < n N := by
    have hnpos : 0 < n N := by unfold n; omega
    exact Nat.cast_pos.mpr hnpos
  have hb := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    realEnergy_log_power_diagonal_ge he (hx i))
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hb
  have hm := div_le_div_of_nonneg_right (neg_le_neg hb)
    (show 0 ≤ 2 * (n N : ℝ) ^ 2 by positivity)
  apply hm.trans_eq
  field_simp [hn.ne']
  ring

theorem realEnergy_sigma_diagonal_sum {N : ℕ} (hN : 0 < N)
    {e : ℝ} (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    {s : Fin (n N) → ℝ} (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1) :
    -(∑ j : Fin (n N), realEnergyCosineKernel (realEnergySigma e (s j) ^ 2) (s j) (s j)) /
        (n N : ℝ) ^ 2 ≤
      -(∑ j : Fin (n N), Real.log (1 - s j)) / (n N : ℝ) ^ 2 +
        (Real.log 2 - 2 * Real.log e) / (n N : ℝ) := by
  have hn : (0 : ℝ) < n N := by
    have hnpos : 0 < n N := by unfold n; omega
    exact Nat.cast_pos.mpr hnpos
  have hb := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
    realEnergy_cosine_sigma_diagonal_lower he (hs j))
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hb
  have hm := div_le_div_of_nonneg_right (neg_le_neg hb) (sq_nonneg (n N : ℝ))
  apply hm.trans_eq
  field_simp [hn.ne']
  ring

end InternalCatalan

end

end OAI
