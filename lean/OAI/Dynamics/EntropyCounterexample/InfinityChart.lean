import Mathlib

namespace OAI

noncomputable section

namespace Problem340.InfinityChart

def update {E : Type*} (C : E → ℂ) (x : E × ℂ) : ℂ :=
  x.2 ^ 2 / (1 + C x.1 * x.2 ^ 2)

@[simp] theorem update_zero {E : Type*} (C : E → ℂ) (p : E) :
    update C (p, 0) = 0 := by
  simp [update]

theorem inverse_affine_square (c w : ℂ) (hw : w ≠ 0) :
    ((w⁻¹) ^ 2 + c)⁻¹ = w ^ 2 / (1 + c * w ^ 2) := by
  have h : (w⁻¹) ^ 2 + c = (1 + c * w ^ 2) / w ^ 2 := by
    field_simp
  rw [h, inv_div]

theorem denominator_norm_lower_bound (c w : ℂ) :
    1 - ‖c‖ * ‖w‖ ^ 2 ≤ ‖1 + c * w ^ 2‖ := by
  have h := norm_sub_norm_le (1 : ℂ) (-(c * w ^ 2))
  have hnorm : ‖c * w ^ 2‖ = ‖c‖ * ‖w‖ ^ 2 := by simp
  rw [norm_one, norm_neg, hnorm, sub_neg_eq_add] at h
  exact h

theorem one_half_lt_denominator_norm {c w : ℂ} {K : ℝ}
    (hc : ‖c‖ ≤ K) (hw : K * ‖w‖ ^ 2 < 1 / 2) :
    (1 : ℝ) / 2 < ‖1 + c * w ^ 2‖ := by
  have hmul := mul_le_mul_of_nonneg_right hc (sq_nonneg ‖w‖)
  have hlower := denominator_norm_lower_bound c w
  linarith

theorem denominator_ne_zero {c w : ℂ}
    (h : ‖c‖ * ‖w‖ ^ 2 < 1) : 1 + c * w ^ 2 ≠ 0 := by
  intro heq
  have hlower := denominator_norm_lower_bound c w
  rw [heq, norm_zero] at hlower
  linarith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {C : E → ℂ} {n : WithTop ℕ∞}

theorem contDiffAt_update {x : E × ℂ} (hC : ContDiffAt ℝ n C x.1)
    (hden : 1 + C x.1 * x.2 ^ 2 ≠ 0) :
    ContDiffAt ℝ n (update C) x := by
  have hw : ContDiffAt ℝ n (fun y : E × ℂ => y.2 ^ 2) x :=
    contDiffAt_snd.pow 2
  have hc : ContDiffAt ℝ n (fun y : E × ℂ => C y.1) x :=
    hC.comp x contDiffAt_fst
  have hd : ContDiffAt ℝ n (fun y : E × ℂ => 1 + C y.1 * y.2 ^ 2) x :=
    contDiffAt_const.add (hc.mul hw)
  change ContDiffAt ℝ n (fun y : E × ℂ => y.2 ^ 2 / (1 + C y.1 * y.2 ^ 2)) x
  simp only [div_eq_mul_inv]
  exact hw.mul (hd.fun_inv hden)

theorem contDiffAt_update_zero {p : E} (hC : ContDiffAt ℝ n C p) :
    ContDiffAt ℝ n (update C) (p, 0) := by
  apply contDiffAt_update hC
  simp

def domain (C : E → ℂ) : Set (E × ℂ) :=
  {x | 1 + C x.1 * x.2 ^ 2 ≠ 0}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
@[simp] theorem zero_mem_domain (C : E → ℂ) (p : E) :
    (p, (0 : ℂ)) ∈ domain C := by
  simp [domain]

omit [NormedSpace ℝ E] in

theorem isOpen_domain (hC : Continuous C) : IsOpen (domain C) := by
  apply isOpen_ne_fun
  · exact continuous_const.add ((hC.comp continuous_fst).mul (continuous_snd.pow 2))
  · exact continuous_const

theorem contDiffOn_update (hC : ContDiff ℝ n C) :
    ContDiffOn ℝ n (update C) (domain C) := by
  intro x hx
  exact (contDiffAt_update hC.contDiffAt hx).contDiffWithinAt

theorem exists_open_contDiffOn_update (hC : ContDiff ℝ n C) (p : E) :
    ∃ U : Set (E × ℂ), IsOpen U ∧ (p, (0 : ℂ)) ∈ U ∧
      ContDiffOn ℝ n (update C) U := by
  exact ⟨domain C, isOpen_domain hC.continuous, zero_mem_domain C p,
    contDiffOn_update hC⟩

end Problem340.InfinityChart

end

end OAI
