import OAI.NumberTheory.DukePrimeDegree.Arithmetic.ZetaIsomorphism
import OAI.NumberTheory.PrimePackets.NormalClosure

namespace OAI

/-!
# The normal-closure simple-zero scale

The discriminant and zero-box bounds provide a fixed positive
scale, depending only on the degree, on which a normal-closure zero is
simple. This converts that statement to the integer multiplicities used
by the descent argument.
-/

noncomputable section
open Module Set
open scoped NumberField Classical

namespace DukePrimeDegree
open PrimeDegreePackets PrimeDegreePackets.HeckeMellin PrimeDegreePackets.AnalyticGrowth

theorem zetaMultiplicity_eq_zeroMultiplicity
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    {d : ℕ} (σ : OrderedEmbeddings (d + 1) K) (hn : finrank ℚ K = d + 1)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    zetaMultiplicity K β = zeroMultiplicity (completedThetaXi σ hn) (β : ℂ) := by
  unfold zetaMultiplicity zeroMultiplicity
  rw [zetaZeroOrder_eq_completed_order σ hn hβ0 hβ1]
  rfl

lemma real_mem_scaled_normalClosure_box
    {D C a β : ℝ} (hD : 0 < D) (hL : 4 ≤ Real.log D) (hC : 0 < C)
    (ha : a ≤ 1 / (8 * C)) (hβ : 1 - a / Real.log D ≤ β) :
    InNearOneBox (C * Real.log (3 * D)) (β : ℂ) := by
  have hLp : 0 < Real.log D := by linarith
  have hlog3 : Real.log 3 ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
    linarith
  have hlog : Real.log (3 * D) = Real.log 3 + Real.log D :=
    Real.log_mul (by norm_num) hD.ne'
  have hlogp : 0 < Real.log (3 * D) := by
    rw [hlog]
    have : 0 < Real.log 3 := Real.log_pos (by norm_num)
    linarith
  have hb : Real.log (3 * D) ≤ 2 * Real.log D := by rw [hlog]; linarith
  have hden : 4 * (C * Real.log (3 * D)) ≤ 8 * C * Real.log D := by nlinarith
  have hfrac := one_div_le_one_div_of_le
    (show 0 < 4 * (C * Real.log (3 * D)) by positivity) hden
  have haL : a / Real.log D ≤ 1 / (8 * C * Real.log D) := by
    calc
      a / Real.log D ≤ (1 / (8 * C)) / Real.log D := div_le_div_of_nonneg_right ha hLp.le
      _ = 1 / (8 * C * Real.log D) := by rw [div_div]
  constructor
  · change 1 - 1 / (4 * (C * Real.log (3 * D))) ≤ β
    linarith
  · change |(0 : ℝ)| ≤ 1 / (4 * (C * Real.log (3 * D)))
    rw [abs_zero]
    positivity

theorem normalClosure_simple_zero_scaled (d : ℕ) :
    ∃ a T : ℝ, 0 < a ∧ a ≤ 1 ∧ 4 ≤ T ∧
      ∀ {K E : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
        [Field E] [NumberField E] [IsNormalClosure ℚ K E] [NumberField.IsTotallyReal E]
        (_σ : OrderedEmbeddings (d + 1) K) (_hn : finrank ℚ K = d + 1),
        T ≤ Real.log |(NumberField.discr K : ℝ)| →
        ∀ β : ℝ, 0 < β → β < 1 →
          1 - a / Real.log |(NumberField.discr K : ℝ)| ≤ β →
          zetaMultiplicity E β ≠ 0 → zetaMultiplicity E β = 1 := by
  obtain ⟨C, T, hC, hT, hzero⟩ := normalClosure_zero_box_uniform d
  refine ⟨min 1 (1 / (8 * C)), max 4 (T + 1), by positivity, min_le_left _ _,
    le_max_left _ _, ?_⟩
  intro K E _ _ _ _ _ _ _ σ hn hL β hβ0 hβ1 hβ hne
  let τ := canonicalRealEmbeddings E
  have he := degreePred_spec E
  have hord := zetaMultiplicity_eq_zeroMultiplicity τ he hβ0 hβ1
  have hEzero : completedThetaXi τ he (β : ℂ) = 0 := by
    apply (zeroMultiplicity_ne_zero_iff (completedThetaXi_entire τ he)
      (dedekindXiZeros_ne_zero_totallyReal τ he) (β : ℂ)).mp
    rwa [← hord]
  have hthreshold : T < Real.log |(NumberField.discr K : ℝ)| := by
    have := le_max_right 4 (T + 1)
    linarith
  have hbox := real_mem_scaled_normalClosure_box
    (abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero K))
    ((le_max_left 4 (T + 1)).trans hL) hC (min_le_right _ _) hβ
  exact hord.trans (hzero σ hn τ he hthreshold (β : ℂ) hEzero hbox).1

end DukePrimeDegree

end

end OAI
