import OAI.Geometry.PeriodicTiling.ScalarAverage
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Module

namespace OAI

noncomputable section

universe uE uInner

namespace PeriodicTilingThree

open Finset Filter
open scoped Topology InnerProductSpace ComplexConjugate

section Normed

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_vectorAverage (u : ℕ → E) (N : ℕ) :
    ‖vectorAverage u N‖ = (N : ℝ)⁻¹ * ‖∑ n ∈ range N, u n‖ := by
  rw [vectorAverage, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N))]

theorem sum_shift_sub_sum {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : ℕ → E) (N h : ℕ) :
    (∑ n ∈ range N, u (n + h)) - (∑ n ∈ range N, u n) =
      (∑ n ∈ range h, u (n + N)) - (∑ n ∈ range h, u n) := by
  have h₁ : (∑ n ∈ range (N + h), u n) =
      (∑ n ∈ range N, u n) + (∑ n ∈ range h, u (n + N)) := by
    simpa only [Nat.add_comm] using sum_range_add u N h
  have h₂ : (∑ n ∈ range (N + h), u n) =
      (∑ n ∈ range h, u n) + (∑ n ∈ range N, u (n + h)) := by
    simpa only [Nat.add_comm] using sum_range_add u h N
  apply sub_eq_sub_iff_add_eq_add.mpr
  simpa only [add_comm] using h₂.symm.trans h₁

theorem norm_sum_range_le_length
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : ℕ → E) (hu : ∀ n, ‖u n‖ ≤ 1) (N : ℕ) :
    ‖∑ n ∈ range N, u n‖ ≤ (N : ℝ) := by
  calc
    _ ≤ ∑ n ∈ range N, ‖u n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ range N, (1 : ℝ) := sum_le_sum fun n _ => hu n
    _ = (N : ℝ) := by simp

theorem norm_shift_sum_sub_le (u : ℕ → E) (hu : ∀ n, ‖u n‖ ≤ 1) (N h : ℕ) :
    ‖(∑ n ∈ range N, u (n + h)) - (∑ n ∈ range N, u n)‖ ≤ 2 * (h : ℝ) := by
  rw [sum_shift_sub_sum]
  calc
    _ ≤ ‖∑ n ∈ range h, u (n + N)‖ + ‖∑ n ∈ range h, u n‖ := norm_sub_le _ _
    _ ≤ (h : ℝ) + h := add_le_add
      (norm_sum_range_le_length (fun n => u (n + N)) (fun n => hu (n + N)) h)
      (norm_sum_range_le_length u hu h)
    _ = 2 * (h : ℝ) := by ring

theorem norm_shift_average_sub_le (u : ℕ → E) (hu : ∀ n, ‖u n‖ ≤ 1) (N h : ℕ) :
    ‖vectorAverage (fun n => u (n + h)) N - vectorAverage u N‖ ≤
      (N : ℝ)⁻¹ * (2 * (h : ℝ)) := by
  simp only [vectorAverage, ← smul_sub]
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N))]
  exact mul_le_mul_of_nonneg_left (norm_shift_sum_sub_le u hu N h) (by positivity)

def smoothedAverage (u : ℕ → E) (H N : ℕ) : E :=
  (H : ℝ)⁻¹ • vectorAverage (fun n => ∑ h ∈ range H, u (n + h)) N

theorem smoothedAverage_eq_sum (u : ℕ → E) (H N : ℕ) :
    smoothedAverage u H N =
      (H : ℝ)⁻¹ • ∑ h ∈ range H, vectorAverage (fun n => u (n + h)) N := by
  simp only [smoothedAverage, vectorAverage, smul_sum]
  rw [sum_comm]

theorem smoothedAverage_sub (u : ℕ → E) {H : ℕ} (hH : 0 < H) (N : ℕ) :
    smoothedAverage u H N - vectorAverage u N =
      (H : ℝ)⁻¹ • ∑ h ∈ range H,
        (vectorAverage (fun n => u (n + h)) N - vectorAverage u N) := by
  have hHr : (H : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hH.ne'
  rw [sum_sub_distrib, smul_sub, ← smoothedAverage_eq_sum]
  congr 1
  simp only [sum_const, card_range, ← Nat.cast_smul_eq_nsmul ℝ,
    smul_smul, inv_mul_cancel₀ hHr, one_smul]

theorem norm_smoothedAverage_sub_le (u : ℕ → E) (hu : ∀ n, ‖u n‖ ≤ 1)
    {H : ℕ} (hH : 0 < H) (N : ℕ) :
    ‖smoothedAverage u H N - vectorAverage u N‖ ≤
      (N : ℝ)⁻¹ * (2 * (H : ℝ)) := by
  have hHr : (H : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hH.ne'
  rw [smoothedAverage_sub u hH N, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg H))]
  have hsum :
      ‖∑ h ∈ range H, (vectorAverage (fun n => u (n + h)) N - vectorAverage u N)‖ ≤
        (H : ℝ) * ((N : ℝ)⁻¹ * (2 * (H : ℝ))) := by
    calc
      _ ≤ ∑ h ∈ range H,
          ‖vectorAverage (fun n => u (n + h)) N - vectorAverage u N‖ := norm_sum_le _ _
      _ ≤ ∑ _h ∈ range H, ((N : ℝ)⁻¹ * (2 * (H : ℝ))) := by
        apply sum_le_sum
        intro h hh
        refine (norm_shift_average_sub_le u hu N h).trans ?_
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hh' : (h : ℝ) ≤ H := by exact_mod_cast (mem_range.mp hh).le
        linarith
      _ = (H : ℝ) * ((N : ℝ)⁻¹ * (2 * (H : ℝ))) := by simp
  calc
    _ ≤ (H : ℝ)⁻¹ * ((H : ℝ) * ((N : ℝ)⁻¹ * (2 * (H : ℝ)))) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (N : ℝ)⁻¹ * (2 * (H : ℝ)) := by
      rw [← mul_assoc, inv_mul_cancel₀ hHr, one_mul]

theorem norm_vectorAverage_sq_le (u : ℕ → E) (N : ℕ) :
    ‖vectorAverage u N‖ ^ 2 ≤ (N : ℝ)⁻¹ * ∑ n ∈ range N, ‖u n‖ ^ 2 := by
  by_cases hN : N = 0
  · simp [hN, vectorAverage]
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hsum : ‖∑ n ∈ range N, u n‖ ^ 2 ≤ (∑ n ∈ range N, ‖u n‖) ^ 2 := by
    have hn : 0 ≤ ∑ n ∈ range N, ‖u n‖ := sum_nonneg fun _ _ => norm_nonneg _
    exact (sq_le_sq₀ (norm_nonneg _) hn).mpr (norm_sum_le (range N) u)
  have hc : (∑ n ∈ range N, ‖u n‖) ^ 2 ≤
      (N : ℝ) * ∑ n ∈ range N, ‖u n‖ ^ 2 := by
    simpa only [card_range] using
      (sq_sum_le_card_mul_sum_sq (s := range N) (f := fun n => ‖u n‖))
  rw [norm_vectorAverage, mul_pow]
  calc
    _ ≤ ((N : ℝ)⁻¹) ^ 2 * ((N : ℝ) * ∑ n ∈ range N, ‖u n‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (hsum.trans hc) (sq_nonneg _)
    _ = (N : ℝ)⁻¹ * ∑ n ∈ range N, ‖u n‖ ^ 2 := by
      field_simp [hNr]

end Normed

section InnerProduct

variable {E : Type uInner} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def offDiagonalAverage (u : ℕ → E) (H N : ℕ) : ℝ :=
  ∑ h ∈ range H, ∑ k ∈ range H,
    if h = k then 0 else vectorAverage (fun n => ⟪u (n + h), u (n + k)⟫_ℝ) N

theorem block_energy_eq (u : ℕ → E) (H N : ℕ) :
    (N : ℝ)⁻¹ * ∑ n ∈ range N, ‖∑ h ∈ range H, u (n + h)‖ ^ 2 =
      ∑ h ∈ range H, ∑ k ∈ range H,
        vectorAverage (fun n => ⟪u (n + h), u (n + k)⟫_ℝ) N := by
  simp only [← real_inner_self_eq_norm_sq, sum_inner, inner_sum,
    vectorAverage, smul_eq_mul, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro h _hh
  rw [sum_comm]
  apply sum_congr rfl
  intro k _hk
  apply sum_congr rfl
  intro n _hn
  rw [real_inner_comm]

theorem diagonal_average_le_one (u : ℕ → E) (hu : ∀ n, ‖u n‖ ≤ 1) (h N : ℕ) :
    vectorAverage (fun n => ⟪u (n + h), u (n + h)⟫_ℝ) N ≤ 1 := by
  by_cases hN : N = 0
  · simp [hN, vectorAverage]
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hb : ∀ n, ⟪u (n + h), u (n + h)⟫_ℝ ≤ 1 := by
    intro n
    rw [real_inner_self_eq_norm_sq]
    simpa only [one_pow] using
      (sq_le_sq₀ (norm_nonneg (u (n + h))) zero_le_one).mpr (hu (n + h))
  simp only [vectorAverage, smul_eq_mul]
  calc
    _ ≤ (N : ℝ)⁻¹ * (∑ _n ∈ range N, (1 : ℝ)) :=
      mul_le_mul_of_nonneg_left (sum_le_sum fun n _ => hb n) (by positivity)
    _ = 1 := by simp [inv_mul_cancel₀ hNr]

theorem block_energy_le (u : ℕ → E) (hu : ∀ n, ‖u n‖ ≤ 1) (H N : ℕ) :
    (N : ℝ)⁻¹ * ∑ n ∈ range N, ‖∑ h ∈ range H, u (n + h)‖ ^ 2 ≤
      (H : ℝ) + offDiagonalAverage u H N := by
  rw [block_energy_eq]
  calc
    _ ≤ ∑ h ∈ range H, (1 + ∑ k ∈ range H,
        if h = k then 0 else vectorAverage (fun n => ⟪u (n + h), u (n + k)⟫_ℝ) N) := by
      apply sum_le_sum
      intro h hh
      calc
        _ ≤ ∑ k ∈ range H,
            ((if h = k then (1 : ℝ) else 0) +
              (if h = k then 0 else vectorAverage (fun n => ⟪u (n + h), u (n + k)⟫_ℝ) N)) := by
          apply sum_le_sum
          intro k _hk
          by_cases he : h = k
          · subst k
            simpa using diagonal_average_le_one u hu h N
          · simp [he]
        _ = _ := by simp [sum_add_distrib, hh]
    _ = (H : ℝ) + offDiagonalAverage u H N := by
      simp [sum_add_distrib, offDiagonalAverage]

theorem norm_smoothedAverage_sq_le (u : ℕ → E) (hu : ∀ n, ‖u n‖ ≤ 1)
    {H : ℕ} (hH : 0 < H) (N : ℕ) :
    ‖smoothedAverage u H N‖ ^ 2 ≤
      (H : ℝ)⁻¹ + ((H : ℝ)⁻¹) ^ 2 * offDiagonalAverage u H N := by
  have hHr : (H : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hH.ne'
  have hb := (norm_vectorAverage_sq_le (fun n => ∑ h ∈ range H, u (n + h)) N).trans
    (block_energy_le u hu H N)
  rw [smoothedAverage, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg H)), mul_pow]
  calc
    _ ≤ ((H : ℝ)⁻¹) ^ 2 * ((H : ℝ) + offDiagonalAverage u H N) :=
      mul_le_mul_of_nonneg_left hb (sq_nonneg _)
    _ = (H : ℝ)⁻¹ + ((H : ℝ)⁻¹) ^ 2 * offDiagonalAverage u H N := by
      field_simp [hHr]

theorem finite_vanDerCorput (u : ℕ → E) (hu : ∀ n, ‖u n‖ ≤ 1)
    {H : ℕ} (hH : 0 < H) (N : ℕ) :
    ‖vectorAverage u N‖ ^ 2 ≤
      2 * ((H : ℝ)⁻¹ + ((H : ℝ)⁻¹) ^ 2 * offDiagonalAverage u H N) +
        2 * ((N : ℝ)⁻¹ * (2 * (H : ℝ))) ^ 2 := by
  have hs := norm_smoothedAverage_sq_le u hu hH N
  have he := norm_smoothedAverage_sub_le u hu hH N
  have ht : ‖vectorAverage u N‖ ≤
      ‖smoothedAverage u H N‖ + ‖smoothedAverage u H N - vectorAverage u N‖ := by
    have ht' := norm_sub_le (smoothedAverage u H N)
      (smoothedAverage u H N - vectorAverage u N)
    simpa only [sub_sub_cancel] using ht'
  have he0 : 0 ≤ (N : ℝ)⁻¹ * (2 * (H : ℝ)) := by positivity
  have hn := norm_nonneg (smoothedAverage u H N)
  have hn' := norm_nonneg (smoothedAverage u H N - vectorAverage u N)
  have hn'' := norm_nonneg (vectorAverage u N)
  have hsq : ‖vectorAverage u N‖ ^ 2 ≤
      2 * ‖smoothedAverage u H N‖ ^ 2 +
        2 * ‖smoothedAverage u H N - vectorAverage u N‖ ^ 2 := by
    have ht₂ := (sq_le_sq₀ hn'' (add_nonneg hn hn')).mpr ht
    nlinarith [sq_nonneg (‖smoothedAverage u H N‖ -
      ‖smoothedAverage u H N - vectorAverage u N‖)]
  have he' : ‖smoothedAverage u H N - vectorAverage u N‖ ^ 2 ≤
      ((N : ℝ)⁻¹ * (2 * (H : ℝ))) ^ 2 := (sq_le_sq₀ hn' he0).mpr he
  linarith

theorem offDiagonalAverage_tendsto_zero (u : ℕ → E)
    (hcor : ∀ h k : ℕ, h ≠ k →
      Tendsto (vectorAverage (fun n => ⟪u (n + h), u (n + k)⟫_ℝ)) atTop (𝓝 0))
    (H : ℕ) : Tendsto (offDiagonalAverage u H) atTop (𝓝 0) := by
  have hk (h k : ℕ) : Tendsto
      (fun N => if h = k then (0 : ℝ) else
        vectorAverage (fun n => ⟪u (n + h), u (n + k)⟫_ℝ) N) atTop (𝓝 0) := by
    by_cases he : h = k
    · simp only [he, ite_true]
      exact tendsto_const_nhds
    · simpa only [he, ite_false] using hcor h k he
  have hh (h : ℕ) : Tendsto
      (fun N => ∑ k ∈ range H, if h = k then (0 : ℝ) else
        vectorAverage (fun n => ⟪u (n + h), u (n + k)⟫_ℝ) N) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum (range H) (fun k _ => hk h k)
  unfold offDiagonalAverage
  simpa only [sum_const_zero] using
    tendsto_finsetSum (range H) (fun h _ => hh h)

theorem vectorAverage_tendsto_zero_of_shift_inner (u : ℕ → E)
    (hu : ∀ n, ‖u n‖ ≤ 1)
    (hcor : ∀ h k : ℕ, h ≠ k →
      Tendsto (vectorAverage (fun n => ⟪u (n + h), u (n + k)⟫_ℝ)) atTop (𝓝 0)) :
    Tendsto (vectorAverage u) atTop (𝓝 0) := by
  have hsq : Tendsto (fun N => ‖vectorAverage u N‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    apply tendsto_order.mpr
    constructor
    · intro a ha
      exact Filter.Eventually.of_forall fun N => lt_of_lt_of_le ha (sq_nonneg _)
    · intro b hb
      obtain ⟨H, hH⟩ := exists_nat_gt (2 / b)
      have hHr : (0 : ℝ) < H := lt_trans (by positivity : (0 : ℝ) < 2 / b) hH
      have hHn : 0 < H := Nat.cast_pos.mp hHr
      have hlimit : 2 * (H : ℝ)⁻¹ < b := by
        have hx : 2 < (H : ℝ) * b := (div_lt_iff₀ hb).mp hH
        have hy : 2 / (H : ℝ) < b := (div_lt_iff₀ hHr).mpr (by nlinarith)
        simpa only [div_eq_mul_inv] using hy
      have hoff := offDiagonalAverage_tendsto_zero u hcor H
      have hfirst : Tendsto
          (fun N => (H : ℝ)⁻¹ + ((H : ℝ)⁻¹) ^ 2 * offDiagonalAverage u H N)
          atTop (𝓝 ((H : ℝ)⁻¹)) := by
        simpa only [mul_zero, add_zero] using
          tendsto_const_nhds.add (hoff.const_mul (((H : ℝ)⁻¹) ^ 2))
      have hsecond : Tendsto (fun N : ℕ => ((N : ℝ)⁻¹ * (2 * (H : ℝ))) ^ 2)
          atTop (𝓝 (0 : ℝ)) := by
        simpa only [zero_mul, zero_pow (by decide : (2 : ℕ) ≠ 0)] using
          (tendsto_inv_atTop_nhds_zero_nat.mul_const (2 * (H : ℝ))).pow 2
      have hg : Tendsto
          (fun N => 2 * ((H : ℝ)⁻¹ + ((H : ℝ)⁻¹) ^ 2 * offDiagonalAverage u H N) +
            2 * ((N : ℝ)⁻¹ * (2 * (H : ℝ))) ^ 2)
          atTop (𝓝 (2 * (H : ℝ)⁻¹)) := by
        simpa only [mul_zero, add_zero] using (hfirst.const_mul 2).add (hsecond.const_mul 2)
      filter_upwards [(tendsto_order.mp hg).2 b hlimit] with N hN
      exact lt_of_le_of_lt (finite_vanDerCorput u hu hHn N) hN
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hsq.sqrt

end InnerProduct

theorem vectorAverage_complex_inner_eq_re (u : ℕ → ℂ) (h k N : ℕ) :
    vectorAverage (fun n => ⟪u (n + h), u (n + k)⟫_ℝ) N =
      (complexAverage (fun n => u (n + k) * conj (u (n + h))) N).re := by
  rw [complexAverage_eq_vectorAverage]
  simp only [vectorAverage, Complex.inner, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.re_sum, smul_eq_mul]

theorem complexAverage_vanDerCorput (u : ℕ → ℂ)
    (hu : ∀ n, ‖u n‖ ≤ 1)
    (hcor : ∀ h k : ℕ, h ≠ k →
      Tendsto (complexAverage (fun n => u (n + h) * conj (u (n + k)))) atTop (𝓝 0)) :
    Tendsto (complexAverage u) atTop (𝓝 0) := by
  have hi : ∀ h k : ℕ, h ≠ k →
      Tendsto (vectorAverage (fun n => ⟪u (n + h), u (n + k)⟫_ℝ)) atTop (𝓝 0) := by
    intro h k hne
    have hr := (Complex.continuous_re.tendsto 0).comp (hcor k h hne.symm)
    simp only [Complex.zero_re] at hr
    convert hr using 1
    · funext N
      exact vectorAverage_complex_inner_eq_re u h k N
  convert vectorAverage_tendsto_zero_of_shift_inner u hu hi using 1
  funext N
  exact complexAverage_eq_vectorAverage u N

end PeriodicTilingThree

end

end OAI
