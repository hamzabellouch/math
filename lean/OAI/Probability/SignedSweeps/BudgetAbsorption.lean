import OAI.Probability.SignedSweeps.BudgetBounds

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped Topology
open Filter

def childDepth (d : ℕ) : ℕ := (d + 1) / 2

lemma childDepth_bounds {d : ℕ} (hd : 4 ≤ d) :
    1 ≤ childDepth d ∧ 4 * childDepth d ≤ 3 * d := by
  unfold childDepth
  omega

lemma coefficient_gap {a : ℝ} (ha : 0 ≤ a) {d : ℕ} (hd : 4 ≤ d) :
    a / (16 * Real.sqrt d) ≤ coefficient a d - coefficient a (childDepth d) := by
  have hcd := childDepth_bounds hd
  have hp : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hcp : (0 : ℝ) < childDepth d := by exact_mod_cast hcd.1
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr hp
  have hcs : 0 < Real.sqrt (childDepth d) := Real.sqrt_pos.mpr hcp
  have ht : 4 * (childDepth d : ℝ) ≤ 3 * d := by exact_mod_cast hcd.2
  have hratio : (9 / 8 : ℝ) * Real.sqrt (childDepth d) ≤ Real.sqrt d := by
    apply (sq_le_sq₀ (by positivity) hs.le).mp
    nlinarith [Real.sq_sqrt hp.le, Real.sq_sqrt hcp.le]
  have hinv : (1 : ℝ) / (16 * Real.sqrt d) ≤
      1 / (2 * Real.sqrt (childDepth d)) - 1 / (2 * Real.sqrt d) := by
    rw [le_sub_iff_add_le]
    field_simp
    nlinarith
  calc
    _ = a * (1 / (16 * Real.sqrt d)) := by ring
    _ ≤ a * (1 / (2 * Real.sqrt (childDepth d)) - 1 / (2 * Real.sqrt d)) :=
      mul_le_mul_of_nonneg_left hinv ha
    _ = _ := by unfold coefficient; ring

lemma nat_two_pow_log (d : ℕ) : Real.log ((2 ^ d : ℕ) : ℝ) = (d : ℝ) * Real.log 2 := by
  rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]

lemma depth_power_error_tendsto {δ ξ : ℝ} (h : δ < ξ) :
    Tendsto (fun d : ℕ => Real.sqrt d * (((2 ^ d : ℕ) : ℝ) ^ (δ - ξ))) atTop (𝓝 0) := by
  have hb : 0 < (ξ - δ) * Real.log 2 := mul_pos (sub_pos.mpr h) (Real.log_pos (by norm_num))
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 / 2) ((ξ - δ) * Real.log 2) hb).comp
    tendsto_natCast_atTop_atTop
  convert ht using 1
  funext d
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by positivity : (0 : ℝ) < (2 ^ d : ℕ)),
    nat_two_pow_log]
  congr 2
  ring

lemma induction_error_absorption {η κ c C δ ξ : ℝ}
    (hη : 0 < η) (hκ : 0 < κ) (hc : 0 < c) (_hC : 0 ≤ C) (hδξ : δ < ξ) :
    ∃ d₀ : ℕ, 4 ≤ d₀ ∧ ∀ d ≥ d₀, ∀ F : ℝ, 0 ≤ F → ∀ l : ℕ,
      c * (((2 ^ d : ℕ) : ℝ) ^ (1 - δ)) ≤
          F + (l : ℝ) * Real.log ((2 ^ d : ℕ) : ℝ) →
      C * ((l : ℝ) + (((2 ^ d : ℕ) : ℝ) ^ (1 - ξ))) ≤
        (coefficient η d - coefficient η (childDepth d)) * F +
          (coefficient κ d - coefficient κ (childDepth d)) *
            ((l : ℝ) * Real.log ((2 ^ d : ℕ) : ℝ)) := by
  let a := min η κ
  have ha : 0 < a := lt_min hη hκ
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ht := (depth_power_error_tendsto hδξ).const_mul C
  have hsmall : ∀ᶠ d : ℕ in atTop,
      C * (Real.sqrt d * (((2 ^ d : ℕ) : ℝ) ^ (δ - ξ))) ≤ a * c / 32 := by
    apply ht.eventually_le_const
    simp only [mul_zero]
    positivity
  have hlinear : ∀ᶠ d : ℕ in atTop, 32 * C / (a * Real.log 2) ≤ Real.sqrt d :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  have hevent : ∀ᶠ d : ℕ in atTop, ∀ F : ℝ, 0 ≤ F → ∀ l : ℕ,
      c * (((2 ^ d : ℕ) : ℝ) ^ (1 - δ)) ≤
          F + (l : ℝ) * Real.log ((2 ^ d : ℕ) : ℝ) →
      C * ((l : ℝ) + (((2 ^ d : ℕ) : ℝ) ^ (1 - ξ))) ≤
        (coefficient η d - coefficient η (childDepth d)) * F +
          (coefficient κ d - coefficient κ (childDepth d)) *
            ((l : ℝ) * Real.log ((2 ^ d : ℕ) : ℝ)) := by
    filter_upwards [eventually_ge_atTop (4 : ℕ), hsmall, hlinear] with d hd hs hl
    intro F hF l hsize
    have hp : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    have hroot : 0 < Real.sqrt d := Real.sqrt_pos.mpr hp
    have hn : (0 : ℝ) < (2 ^ d : ℕ) := by positivity
    have hln : 0 ≤ Real.log ((2 ^ d : ℕ) : ℝ) := by
      rw [nat_two_pow_log]
      positivity
    have hnormal : a / (32 * Real.sqrt d) * Real.log ((2 ^ d : ℕ) : ℝ) =
        a * Real.log 2 * Real.sqrt d / 32 := by
      rw [nat_two_pow_log]
      field_simp [hroot.ne']
      exact (Real.sq_sqrt hp.le).symm
    have hlin : C ≤ a / (32 * Real.sqrt d) * Real.log ((2 ^ d : ℕ) : ℝ) := by
      rw [hnormal]
      have h := (div_le_iff₀ (mul_pos ha hlog2)).mp hl
      nlinarith
    have hlin' : C * (l : ℝ) ≤ a / (32 * Real.sqrt d) *
        ((l : ℝ) * Real.log ((2 ^ d : ℕ) : ℝ)) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_right hlin (Nat.cast_nonneg l)
    have hpows : (((2 ^ d : ℕ) : ℝ) ^ (δ - ξ)) *
        (((2 ^ d : ℕ) : ℝ) ^ (1 - δ)) = (((2 ^ d : ℕ) : ℝ) ^ (1 - ξ)) := by
      rw [← Real.rpow_add hn]
      congr 1
      ring
    have hsub : C * (((2 ^ d : ℕ) : ℝ) ^ (1 - ξ)) ≤
        a / (32 * Real.sqrt d) * (c * (((2 ^ d : ℕ) : ℝ) ^ (1 - δ))) := by
      apply (mul_le_mul_iff_of_pos_left hroot).mp
      calc
        _ = (C * (Real.sqrt d * (((2 ^ d : ℕ) : ℝ) ^ (δ - ξ)))) *
            (((2 ^ d : ℕ) : ℝ) ^ (1 - δ)) := by
          rw [mul_assoc C, mul_assoc (Real.sqrt d), hpows]
          ring
        _ ≤ (a * c / 32) * (((2 ^ d : ℕ) : ℝ) ^ (1 - δ)) :=
          mul_le_mul_of_nonneg_right hs (Real.rpow_nonneg hn.le _)
        _ = _ := by field_simp
    have hsub' := hsub.trans (mul_le_mul_of_nonneg_left hsize
      (show 0 ≤ a / (32 * Real.sqrt d) by positivity))
    have hηgap : a / (16 * Real.sqrt d) ≤ coefficient η d - coefficient η (childDepth d) :=
      (div_le_div_of_nonneg_right (min_le_left η κ) (by positivity)).trans (coefficient_gap hη.le hd)
    have hκgap : a / (16 * Real.sqrt d) ≤ coefficient κ d - coefficient κ (childDepth d) :=
      (div_le_div_of_nonneg_right (min_le_right η κ) (by positivity)).trans (coefficient_gap hκ.le hd)
    calc
      _ = C * (l : ℝ) + C * (((2 ^ d : ℕ) : ℝ) ^ (1 - ξ)) := by ring
      _ ≤ a / (32 * Real.sqrt d) * ((l : ℝ) * Real.log ((2 ^ d : ℕ) : ℝ)) +
          a / (32 * Real.sqrt d) * (F + (l : ℝ) * Real.log ((2 ^ d : ℕ) : ℝ)) :=
        add_le_add hlin' hsub'
      _ ≤ a / (16 * Real.sqrt d) * (F + (l : ℝ) * Real.log ((2 ^ d : ℕ) : ℝ)) := by
        have hu : 0 ≤ a / (32 * Real.sqrt d) * F := by positivity
        have heq : a / (16 * Real.sqrt d) = 2 * (a / (32 * Real.sqrt d)) := by ring
        rw [heq]
        nlinarith
      _ = a / (16 * Real.sqrt d) * F +
          a / (16 * Real.sqrt d) * ((l : ℝ) * Real.log ((2 ^ d : ℕ) : ℝ)) := by ring
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right hηgap hF)
        (mul_le_mul_of_nonneg_right hκgap (mul_nonneg (Nat.cast_nonneg l) hln))
  obtain ⟨D, hD⟩ := eventually_atTop.mp hevent
  exact ⟨max D 4, le_max_right _ _, fun d hd => hD d ((le_max_left _ _).trans hd)⟩

lemma scalar_induction_budget {η κ c C δ ξ : ℝ}
    (hη : 0 < η) (hκ : 0 < κ) (hc : 0 < c) (hC : 0 ≤ C) (hδξ : δ < ξ) :
    ∃ d₀ : ℕ, 4 ≤ d₀ ∧ ∀ d ≥ d₀, ∀ F : ℝ, 0 ≤ F → ∀ l : ℕ,
      c * (((2 ^ d : ℕ) : ℝ) ^ (1 - δ)) ≤
          F + (l : ℝ) * Real.log ((2 ^ d : ℕ) : ℝ) →
      coefficient η (childDepth d) * F +
          coefficient κ (childDepth d) * l * Real.log ((2 ^ d : ℕ) : ℝ) -
          (l : ℝ) * Real.log (((2 ^ d : ℕ) : ℝ) / l) +
          C * ((l : ℝ) + (((2 ^ d : ℕ) : ℝ) ^ (1 - ξ))) ≤
        coefficient η d * F + remainderBudget κ d l := by
  obtain ⟨d₀, hd₀, hstep⟩ := induction_error_absorption hη hκ hc hC hδξ
  refine ⟨d₀, hd₀, ?_⟩
  intro d hd F hF l hsize
  have he := hstep d hd F hF l hsize
  have hb : coefficient κ d * l * Real.log ((2 ^ d : ℕ) : ℝ) -
      (l : ℝ) * Real.log (((2 ^ d : ℕ) : ℝ) / l) ≤ remainderBudget κ d l := by
    rw [remainderBudget_eq_clippedBudget]
    exact le_max_right 0 _
  nlinarith

end SignedSweeps
end

end OAI
