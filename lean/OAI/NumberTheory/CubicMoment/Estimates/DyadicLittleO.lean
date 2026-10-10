import OAI.NumberTheory.CubicMoment.Estimates.DyadicReconstruction
import OAI.NumberTheory.CubicMoment.Estimates.DyadicScaleBounds

namespace OAI

/-! Summing a dyadic little-oh estimate at the Patterson scale. The
local growth and the vanishing at small arguments are retained explicitly. -/
noncomputable section
open Filter Asymptotics
open scoped BigOperators Topology
namespace CubicFirstMoment

lemma dyadicDifference_regularized_bound (F : ℝ → ℂ) {M : ℝ}
    (hM : 0 ≤ M)
    (hlocal : ∀ X : ℝ, 1 ≤ X → ‖dyadicDifference F X‖ ≤ M*X)
    (hsmall : dyadicDifference F =o[atTop] firstMomentScale) :
    ∃ K : ℝ, 0 < K ∧ ∀ X : ℝ, 1 ≤ X →
      ‖dyadicDifference F X‖ ≤ K*regularizedMomentScale X := by
  obtain ⟨B₀,hB₀⟩ := eventually_atTop.mp (hsmall.def (by norm_num : (0:ℝ) < 1))
  let B := max B₀ (Real.exp 1)
  have hBexp : Real.exp 1 ≤ B := le_max_right _ _
  have hB : 1 < B := (Real.one_lt_exp_iff.mpr (by norm_num : (0:ℝ) < 1)).trans_le hBexp
  have hlogB : 0 < Real.log B := Real.log_pos hB
  let K := 2+M*B*(1+Real.log B)
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K,hK,?_⟩
  intro X hX
  have hXL : 0 < 1+Real.log X := by linarith [Real.log_nonneg hX]
  by_cases hBX : B ≤ X
  · have hLX : 1 ≤ Real.log X := by
      have hh := Real.strictMonoOn_log.monotoneOn
        (Real.exp_pos 1) (zero_lt_one.trans_le hX) (hBexp.trans hBX)
      simpa only [Real.log_exp] using hh
    have hscale := firstMomentScale_le_two_regularized (zero_lt_one.trans_le hX) hLX
    have hb := hB₀ X ((le_max_left _ _).trans hBX)
    have hXp : 1 < X := hB.trans_le hBX
    rw [one_mul,Real.norm_of_nonneg (firstMomentScale_pos hXp).le] at hb
    apply (hb.trans hscale).trans
    apply mul_le_mul_of_nonneg_right _ (regularizedMomentScale_pos hX).le
    have hn : 0 ≤ M*B*(1+Real.log B) := by positivity
    dsimp [K]
    linarith
  · have hXB : X ≤ B := (lt_of_not_ge hBX).le
    rw [regularizedMomentScale,←mul_div_assoc]
    apply (le_div_iff₀ hXL).mpr
    calc
      _ ≤ (M*X)*(1+Real.log X) := mul_le_mul_of_nonneg_right (hlocal X hX) hXL.le
      _ ≤ (M*B)*(1+Real.log B) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hXB hM)
          (by linarith [Real.strictMonoOn_log.monotoneOn (zero_lt_one.trans_le hX) (zero_lt_one.trans hB) hXB])
          hXL.le (by positivity)
      _ ≤ K := by dsimp [K]; linarith
      _ ≤ K*X^(5/6:ℝ) := le_mul_of_one_le_right hK.le
        (Real.one_le_rpow hX (by norm_num))

theorem dyadic_littleO_firstMoment (F : ℝ → ℂ)
    (hF : ∀ X : ℝ, X < 1 → F X = 0) {M : ℝ} (hM : 0 ≤ M)
    (hlocal : ∀ X : ℝ, 1 ≤ X → ‖dyadicDifference F X‖ ≤ M*X)
    (hsmall : dyadicDifference F =o[atTop] firstMomentScale) :
    F =o[atTop] firstMomentScale := by
  obtain ⟨K,hK,hglobal⟩ := dyadicDifference_regularized_bound F hM hlocal hsmall
  let f (X : ℝ) (j : ℕ) : ℂ :=
    dyadicDifference F (X/(2:ℝ)^j)/(firstMomentScale X:ℂ)
  have hpoint (j : ℕ) : Tendsto (fun X => f X j) atTop (𝓝 0) := by
    have ht : Tendsto (fun X : ℝ => X/(2:ℝ)^j) atTop atTop :=
      tendsto_id.atTop_div_const (by positivity)
    have hg := firstMomentScale_dyadic_isBigO j
    have hc := (hsmall.comp_tendsto ht).trans_isBigO hg
    have hz := hc.tendsto_inv_smul_nhds_zero
    simpa only [f,Function.comp_apply,Complex.real_smul,Complex.ofReal_inv,div_eq_mul_inv,mul_comm] using hz
  have hbound : ∀ᶠ X : ℝ in atTop, ∀ j : ℕ, ‖f X j‖ ≤ K*dyadicMomentRatio j := by
    filter_upwards [eventually_gt_atTop (1:ℝ)] with X hX
    intro j
    have hXp : 0 < X := zero_lt_one.trans hX
    have hYp : 0 < X/(2:ℝ)^j := div_pos hXp (by positivity)
    by_cases hY : 1 ≤ X/(2:ℝ)^j
    · dsimp only [f]
      rw [norm_div,Complex.norm_real,Real.norm_of_nonneg (firstMomentScale_pos hX).le]
      calc
        _ ≤ (K*regularizedMomentScale (X/(2:ℝ)^j))/firstMomentScale X :=
          div_le_div_of_nonneg_right (hglobal _ hY) (firstMomentScale_pos hX).le
        _ = K*(regularizedMomentScale (X/(2:ℝ)^j)/firstMomentScale X) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (regularized_dyadic_scale hX j hY) hK.le
    · have hY' : X/(2:ℝ)^j < 1 := lt_of_not_ge hY
      have hz : dyadicDifference F (X/(2:ℝ)^j) = 0 := by
        rw [dyadicDifference,hF _ hY',hF _ (by linarith),sub_self]
      dsimp only [f]
      rw [hz,zero_div,norm_zero]
      unfold dyadicMomentRatio
      positivity [Real.log_pos (by norm_num : (1:ℝ) < 2)]
  have ht := tendsto_tsum_of_dominated_convergence (dyadicMomentRatio_summable.mul_left K)
    hpoint hbound
  simp only [tsum_zero] at ht
  have hf : (fun X : ℝ => ∑' j : ℕ, f X j) =
      fun X => F X/(firstMomentScale X:ℂ) := by
    funext X
    rw [show (∑' j : ℕ, f X j) = (∑' j : ℕ, dyadicDifference F (X/(2:ℝ)^j))/
      (firstMomentScale X:ℂ) by exact tsum_div_const,
      dyadicDifference_reconstruct F hF X]
  rw [hf] at ht
  have hc : F =o[atTop] (fun X => (firstMomentScale X:ℂ)) := by
    apply (isLittleO_iff_tendsto' ?_).mpr ht
    filter_upwards [eventually_gt_atTop (1:ℝ)] with X hX
    exact fun hz => False.elim ((Complex.ofReal_ne_zero.mpr (firstMomentScale_pos hX).ne') hz)
  apply IsLittleO.of_norm_right
  simpa only [Complex.norm_real] using hc.norm_right

end CubicFirstMoment

end

end OAI
