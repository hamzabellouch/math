import OAI.Analysis.MarkovType.FinitePredictableTransform
import OAI.Analysis.MarkovType.FiniteMartingaleMaximal
import OAI.Analysis.MarkovType.TailMoment
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

namespace OAI

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace MarkovSuperreflexivity

variable {Ω E : Type*} [Fintype Ω]

namespace FiniteLaw

private theorem prob_nonneg (μ : FiniteLaw Ω) (A : Ω → Prop) : 0 ≤ μ.prob A := by
  apply Finset.sum_nonneg
  intro ω _
  by_cases h : A ω
  · simpa only [ite_eq_left h] using μ.mass_nonneg ω
  · simp only [ite_eq_right h, le_refl]

private theorem prob_le_one (μ : FiniteLaw Ω) (A : Ω → Prop) : μ.prob A ≤ 1 := by
  calc
    _ ≤ ∑ ω, μ.mass ω := by
      apply Finset.sum_le_sum
      intro ω _
      by_cases h : A ω
      · simp only [ite_eq_left h, le_refl]
      · simpa only [ite_eq_right h] using μ.mass_nonneg ω
    _ = 1 := μ.sum_mass

theorem prob_le_add_of_imp_or (μ : FiniteLaw Ω) (A C D : Ω → Prop)
    (h : ∀ ω, A ω → C ω ∨ D ω) : μ.prob A ≤ μ.prob C + μ.prob D := by
  unfold prob
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro ω _
  by_cases hA : A ω
  · rcases h ω hA with hC | hD
    · by_cases hD : D ω <;> simp only [ite_eq_left hA, ite_eq_left hC, hD, ite_true, ite_false]
      · exact le_add_of_nonneg_right (μ.mass_nonneg ω)
      · simp only [add_zero, le_refl]
    · by_cases hC : C ω <;> simp only [ite_eq_left hA, ite_eq_left hD, hC, ite_true, ite_false]
      · exact le_add_of_nonneg_left (μ.mass_nonneg ω)
      · simp only [zero_add, le_refl]
  · simp only [ite_eq_right hA]
    exact add_nonneg (by split_ifs <;> first | exact μ.mass_nonneg ω | exact le_rfl)
      (by split_ifs <;> first | exact μ.mass_nonneg ω | exact le_rfl)

end FiniteLaw

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem finite_budget_maximal_prob_le (μ : FiniteLaw Ω)
    (F : FinitePartitionFiltration Ω) (d : ℕ → Ω → E) (w : ℕ → Ω → ℝ)
    (N : ℕ) {S t : ℝ} (hS : 0 < S) (ht : 0 < t)
    (hadapt : ∀ j, 0 < j → j ≤ N → F.AdaptedAt j (d j))
    (hzero : ∀ j, 0 < j → j ≤ N →
      HasZeroConditionalSum μ (F.part (j - 1)) (d j))
    (hw : ∀ j ω, 0 ≤ w j ω)
    (hwpred : ∀ j, 0 < j → j ≤ N → F.AdaptedAt (j - 1) (w j)) :
    μ.prob (fun ω => ∃ j : ℕ, j ≤ N ∧ t < ‖partialSumProcess d j ω‖) ≤
      μ.expect (cumulativeCost w N) / S +
        finiteL2Norm μ
          (partialSumProcess (fun j ω => budgetCoefficient w S j ω • d j ω) N) ^
            (2 : ℕ) / t ^ (2 : ℕ) := by
  let M := partialSumProcess (fun j ω => budgetCoefficient w S j ω • d j ω)
  have hM : F.IsMartingaleUpTo μ M N :=
    budgetTransform_isMartingale F μ d w N S hadapt hzero hwpred
  have hcost : ∀ ω, 0 ≤ cumulativeCost w N ω := by
    intro ω
    exact Finset.sum_nonneg (fun j _ => hw (j + 1) ω)
  have hmarkov : S * μ.prob (fun ω => S ≤ cumulativeCost w N ω) ≤
      μ.expect (cumulativeCost w N) := by
    simpa only [Real.rpow_one] using
      μ.tail_power_mul_prob_le (cumulativeCost w N) hcost hS.le
        (show (0 : ℝ) ≤ 1 by norm_num)
  have hmax := finite_martingale_maximal_sq_le_l2 hM ht
  calc
    _ ≤ μ.prob (fun ω => S ≤ cumulativeCost w N ω) +
        μ.prob (fun ω => ∃ j : ℕ, j ≤ N ∧ t < ‖M j ω‖) := by
      apply μ.prob_le_add_of_imp_or
      intro ω hω
      by_cases hbad : S ≤ cumulativeCost w N ω
      · exact Or.inl hbad
      · right
        obtain ⟨j, hjN, hj⟩ := hω
        refine ⟨j, hjN, ?_⟩
        have heq : M j ω = partialSumProcess d j ω :=
          budgetTransform_eq_of_cost_le d w hw hjN (le_of_lt (lt_of_not_ge hbad))
        rwa [heq]
    _ ≤ _ := by
      apply add_le_add
      · apply (le_div_iff₀ hS).mpr
        simpa only [mul_comm] using hmarkov
      · apply (le_div_iff₀ (sq_pos_of_pos ht)).mpr
        simpa only [mul_comm] using hmax

theorem finite_budget_truncation_tail (μ : FiniteLaw Ω)
    (F : FinitePartitionFiltration Ω) (d : ℕ → Ω → E) (N : ℕ)
    {a B : ℝ} (ha : 1 < a) (ha2 : a ≤ 2) (hB : 0 ≤ B)
    (hadapt : ∀ j, 0 < j → j ≤ N → F.AdaptedAt j (d j))
    (hzero : ∀ j, 0 < j → j ≤ N →
      HasZeroConditionalSum μ (F.part (j - 1)) (d j))
    (hnorm : ∀ j, 0 < j → j ≤ N →
      F.AdaptedAt (j - 1) (fun ω => ‖d j ω‖))
    (henergy : μ.expect (cumulativeCost (fun j ω => ‖d j ω‖ ^ a) N) ≤ 1)
    (hBound : ∀ s : ℝ, 0 < s →
      finiteL2Norm μ (partialSumProcess (fun j ω =>
        budgetCoefficient (fun k η => ‖d k η‖ ^ a) (s ^ a) j ω • d j ω) N) ≤ B * s)
    {t : ℝ} (ht : 0 < t) :
    μ.prob (fun ω => ∃ j : ℕ, j ≤ N ∧ t < ‖partialSumProcess d j ω‖) ≤
      (1 + B ^ (2 : ℕ)) / t ^ (a / 2) := by
  have hw : ∀ j ω, 0 ≤ ‖d j ω‖ ^ a :=
    fun j ω => Real.rpow_nonneg (norm_nonneg _) _
  have hwpred : ∀ j, 0 < j → j ≤ N →
      F.AdaptedAt (j - 1) (fun ω => ‖d j ω‖ ^ a) := by
    intro j hj hjN ω η hωη
    exact congrArg (fun x : ℝ => x ^ a) (hnorm j hj hjN hωη)
  have htPow : 0 < t ^ (a / 2) := Real.rpow_pos_of_pos ht _
  by_cases ht1 : 1 ≤ t
  · have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
    have hsPow : 0 < (Real.sqrt t) ^ a := Real.rpow_pos_of_pos hs _
    have hsq := (sq_le_sq₀
      (finiteL2Norm_nonneg μ (partialSumProcess (fun j ω =>
        budgetCoefficient (fun k η => ‖d k η‖ ^ a) ((Real.sqrt t) ^ a) j ω •
          d j ω) N)) (mul_nonneg hB hs.le)).mpr (hBound (Real.sqrt t) hs)
    have hsplit := finite_budget_maximal_prob_le μ F d (fun j ω => ‖d j ω‖ ^ a)
      N hsPow ht hadapt hzero hw hwpred
    have hroot : (Real.sqrt t) ^ a = t ^ (a / 2) :=
      (Real.rpow_div_two_eq_sqrt a ht.le).symm
    have hquot : (B * Real.sqrt t) ^ (2 : ℕ) / t ^ (2 : ℕ) =
        B ^ (2 : ℕ) / t := by
      rw [mul_pow, Real.sq_sqrt ht.le]
      field_simp [ne_of_gt ht]
    have hden : t ^ (a / 2) ≤ t := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le ht1 (show a / 2 ≤ 1 by linarith)
    calc
      _ ≤ 1 / (Real.sqrt t) ^ a +
          (B * Real.sqrt t) ^ (2 : ℕ) / t ^ (2 : ℕ) :=
        hsplit.trans (add_le_add
          (div_le_div_of_nonneg_right henergy hsPow.le)
          (div_le_div_of_nonneg_right hsq (sq_nonneg t)))
      _ = 1 / t ^ (a / 2) + B ^ (2 : ℕ) / t := by rw [hroot, hquot]
      _ ≤ 1 / t ^ (a / 2) + B ^ (2 : ℕ) / t ^ (a / 2) :=
        add_le_add le_rfl (div_le_div_of_nonneg_left (sq_nonneg B) htPow hden)
      _ = _ := (add_div _ _ _).symm
  · apply (μ.prob_le_one _).trans
    apply (le_div_iff₀ htPow).mpr
    simp only [one_mul]
    exact (Real.rpow_le_one ht.le (le_of_lt (lt_of_not_ge ht1))
      (by linarith : 0 ≤ a / 2)).trans (le_add_of_nonneg_right (sq_nonneg B))

end MarkovSuperreflexivity

end

end OAI
