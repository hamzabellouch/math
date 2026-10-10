import OAI.NumberTheory.JointDickman.Counting.CountingForwardEnergy

namespace OAI

/-! # Recovering a symmetric quadratic form from its forward rows -/
namespace JointDickman
open Finset Classical

noncomputable def forwardKernelRow {M : ℕ} (K : Fin M → Fin M → ℝ)
    (z : Fin M → ℂ) (i : Fin M) : ℂ :=
  ∑ k, if i < k then (K i k : ℂ)*star (z i)*z k else 0

theorem complexEnergy_eq_forward_add_star {M : ℕ} (K : Fin M → Fin M → ℝ)
    (hK : ∀ i k, K i k = K k i) (hdiag : ∀ i, K i i = 0) (z : Fin M → ℂ) :
    complexEnergy K z = (∑ i, forwardKernelRow K z i)+star (∑ i, forwardKernelRow K z i) := by
  have hback : star (∑ i, forwardKernelRow K z i) =
      ∑ i, ∑ k, if k < i then (K i k : ℂ)*star (z i)*z k else 0 := by
    simp only [forwardKernelRow,star_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro k _
    by_cases h : k < i
    · simp only [ite_eq_left h,star_mul,Complex.star_def,Complex.conj_ofReal,starRingEnd_self_apply]
      rw [hK k i]
      ring
    · simp only [ite_eq_right h,star_zero]
  rw [hback]
  simp only [complexEnergy,forwardKernelRow,← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro k _
  rcases lt_trichotomy i k with h | rfl | h
  · simp [h,not_lt_of_ge h.le]
  · simp [hdiag]
  · simp [h,not_lt_of_ge h.le]

theorem normalized_complexEnergy_sq_le_forward {M : ℕ} (hM : 0 < M)
    (K : Fin M → Fin M → ℝ) (hK : ∀ i k, K i k = K k i)
    (hdiag : ∀ i, K i i = 0) (z : Fin M → ℂ) :
    (‖complexEnergy K z‖/(M : ℝ))^2 ≤
      (4/(M : ℝ))*(∑ i, ‖forwardKernelRow K z i‖^2) := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hn : ‖complexEnergy K z‖ ≤ 2*‖∑ i, forwardKernelRow K z i‖ := by
    rw [complexEnergy_eq_forward_add_star K hK hdiag]
    exact (norm_add_le _ _).trans_eq (by rw [norm_star]; ring)
  have hs := finite_weighted_square_bound (univ : Finset (Fin M))
    (fun _ => (1 : ℂ)) (forwardKernelRow K z) (C := 1) (by simp)
  simp only [one_mul,card_univ,Fintype.card_fin,one_pow,mul_one] at hs
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hn 2
  rw [div_pow]
  apply (div_le_iff₀ (sq_pos_of_pos hMr)).mpr
  field_simp
  nlinarith

theorem symmetric_energy_square_mean {M : ℕ} (hM : 0 < M) (S : Finset ℕ)
    (K : ℕ → Fin M → Fin M → ℝ) (z : ℕ → Fin M → ℂ)
    (hK : ∀ u i k, K u i k = K u k i) (hdiag : ∀ u i, K u i i = 0)
    {X δ : ℝ} (hX : 0 < X)
    (hrow : ∀ i, (1/X)*(∑ u ∈ S, ‖forwardKernelRow (K u) (z u) i‖^2) ≤ δ) :
    (1/X)*(∑ u ∈ S, (‖complexEnergy (K u) (z u)‖/(M : ℝ))^2) ≤ 4*δ := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  calc
    _ ≤ (1/X)*(∑ u ∈ S, (4/(M : ℝ))*∑ i, ‖forwardKernelRow (K u) (z u) i‖^2) :=
      mul_le_mul_of_nonneg_left (sum_le_sum (fun u _ =>
        normalized_complexEnergy_sq_le_forward hM (K u) (hK u) (hdiag u) (z u))) (by positivity)
    _ = (4/(M : ℝ))*∑ i, (1/X)*(∑ u ∈ S, ‖forwardKernelRow (K u) (z u) i‖^2) := by
      simp only [mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro u _
      ring
    _ ≤ (4/(M : ℝ))*∑ _i : Fin M, δ :=
      mul_le_mul_of_nonneg_left (sum_le_sum (fun i _ => hrow i)) (by positivity)
    _ = _ := by simp; field_simp

end JointDickman

end OAI
