import OAI.Combinatorics.HadwigerCounterexample.FiniteLaws
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic.FieldSimp

namespace OAI

/-! # Finite Entropy -/

noncomputable section
namespace HadwigerCounterexample

open scoped BigOperators
open Real

variable {α : Type*} [Fintype α]

def negEnt (w : Wgt α) : ℝ := ∑ x, w x * Real.log (w x)
def midLaw (w v : Wgt α) : Wgt α := fun x => (w x + v x) * 2⁻¹

@[fun_prop] theorem tot_continuous : Continuous (tot : Wgt α → ℝ) := by
  unfold tot; fun_prop
@[fun_prop] theorem pr_continuous (p : α → Prop) : Continuous (pr (α := α) · p) := by
  unfold pr avg; fun_prop
@[fun_prop] theorem negEnt_continuous : Continuous (negEnt : Wgt α → ℝ) := by
  unfold negEnt
  exact continuous_finsetSum _ fun x _ => Real.continuous_mul_log.comp (continuous_apply x)

theorem closed_isLaw : IsClosed {w : Wgt α | IsLaw w} := by
  have he :
      {w : Wgt α | IsLaw w} =
        (⋂ x : α, {w | 0 ≤ w x}) ∩ {w : Wgt α | tot w = 1} := by
    ext w; simp
    constructor
    · intro hw
      exact ⟨hw.nz, hw.total⟩
    · rintro ⟨h,g⟩
      exact ⟨h,g⟩
  rw [he]
  refine (isClosed_iInter (fun x => ?_)).inter (isClosed_eq tot_continuous continuous_const)
  exact isClosed_le continuous_const (continuous_apply x)

theorem compact_isLaw : IsCompact {w : Wgt α | IsLaw w} := by
  refine IsCompact.of_isClosed_subset (s := Set.Icc (0 : Wgt α) 1) isCompact_Icc
    closed_isLaw ?_
  intro w hw
  exact ⟨hw.nz, hw.weight_le_one⟩

theorem negEnt_le_zero {w : Wgt α} (hw : SubLaw w) : negEnt w ≤ 0 := by
  refine Finset.sum_nonpos fun x _ => mul_nonpos_of_nonneg_of_nonpos (hw.nz x) ?_
  exact Real.log_nonpos (hw.nz x) (hw.weight_le_one x)

private theorem log_bound {m x : ℝ} (hm : 0 < m) (hx : 0 ≤ x) :
    x * (1 - Real.log m) - m⁻¹ ≤ x * Real.log x := by
  rcases lt_or_eq_of_le hx with h | h
  · have hp := Real.self_sub_one_le_mul_log (show 0 ≤ m*x from mul_nonneg hm.le hx)
    rw [Real.log_mul hm.ne' h.ne'] at hp
    apply (mul_le_mul_iff_right₀ hm).mp

    have hi := mul_inv_cancel₀ hm.ne'
    nlinarith only [hp, hi]
  · rw [← h]
    have := inv_pos.mpr hm
    linarith

theorem log_card_le_negEnt [Nonempty α] {w : Wgt α} (hw : IsLaw w) :
    -Real.log (Fintype.card α) ≤ negEnt w := by
  let m := (Fintype.card α : ℝ)
  have hm : 0 < m := by simp [m, Fintype.card_pos]
  have h1 :
      ∑ x, (w x * (1 - Real.log m) - m⁻¹) ≤ negEnt w :=
    Finset.sum_le_sum fun x _ => log_bound hm (hw.nz x)
  have hs : ∑ x, w x = 1 := hw.total
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hs, one_mul, Finset.sum_const] at h1
  simp only [Finset.card_univ, nsmul_eq_mul] at h1
  change 1 - Real.log m - m * m⁻¹ ≤ _ at h1
  rw [mul_inv_cancel₀ hm.ne'] at h1
  change -Real.log m ≤ _
  linarith

private theorem negEnt_gap_elem {x y : ℝ} (h : 0 ≤ x) (g : 0 ≤ y) :
    0 ≤ x * Real.log x + y * Real.log y
      - 2 * (((x + y)*2⁻¹) * Real.log ((x + y)*2⁻¹)) := by
  have hh := Real.convexOn_mul_log.2 (Set.mem_Ici.mpr h) (Set.mem_Ici.mpr g)
    (by norm_num : 0 ≤ (2:ℝ)⁻¹) (by norm_num : 0 ≤ (2:ℝ)⁻¹) (by norm_num)
  simp only [smul_eq_mul] at hh
  rw [show 2⁻¹*x+2⁻¹*y = (x+y)*2⁻¹ by ring] at hh
  linarith

private theorem negEnt_gap_on_zero {x : ℝ} (hx : 0 ≤ x) :
    x * Real.log x - 2 * ((x * 2⁻¹) * Real.log (x * 2⁻¹)) = x * Real.log 2 := by
  rcases lt_or_eq_of_le hx with h | h
  · rw [Real.log_mul h.ne' (by norm_num), Real.log_inv]; ring
  · rw [← h]; ring

/-- Mixing two laws incurs a quantified entropy gap if one gives mass to a set
missed by the other. This midpoint bound suffices without a support lemma. -/
theorem negEnt_gap {w v : Wgt α} (hw : ∀ x, 0 ≤ w x) (hv : ∀ x, 0 ≤ v x)
    (p : α → Prop) (hp : ∀ x, p x → v x = 0) :
    pr w p * Real.log 2 ≤ negEnt w + negEnt v - 2 * negEnt (midLaw w v) := by
  unfold pr avg negEnt
  rw [Finset.sum_mul, ← Finset.sum_add_distrib, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun x _ => ?_
  by_cases hx : p x
  · simp only [hp x hx, ind_one hx, mul_one, midLaw, add_zero, zero_mul]
    rw [negEnt_gap_on_zero (hw x)]
  · simp only [ind_zero hx, mul_zero, zero_mul]
    exact negEnt_gap_elem (hw _) (hv _)

theorem mid_tot (w v : Wgt α) : tot (midLaw w v) = (tot w + tot v) * 2⁻¹ := by
  rw [tot, tot, tot, ← Finset.sum_add_distrib, Finset.sum_mul]
  rfl

theorem midLaw_pr (w v : Wgt α) (p : α → Prop) :
    pr (midLaw w v) p = (pr w p + pr v p) * 2⁻¹ := by
  unfold pr
  rw [avg_comm, avg_comm w, avg_comm v]
  change avg _ (fun x => (w x + v x) * 2⁻¹) = _
  rw [avg_mul, avg_add]

theorem mid_isLaw {w v : Wgt α} (hw : IsLaw w) (hv : IsLaw v) : IsLaw (midLaw w v) := by
  refine ⟨fun x => mul_nonneg (add_nonneg (hw.nz x) (hv.nz x)) (by norm_num), ?_⟩
  rw [mid_tot, hw.total, hv.total]; norm_num

end HadwigerCounterexample

end

end OAI
