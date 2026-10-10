import OAI.NumberTheory.CubicMoment.Estimates.IndependentMellinTail
import OAI.NumberTheory.CubicMoment.Estimates.FullMellinMoment

namespace OAI

/-! Finite-row L2 transfer for independently separated norm weights, with a
proved tail outside the simultaneous height window. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

omit [DecidableEq ι] in
lemma finite_box_integral_moment (f : κ → (ι → ℝ) → ℂ)
    (hf : ∀ r, Continuous (f r)) (w : (ι → ℝ) → ℂ) (hw : Integrable w)
    (T B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ τ ∈ mellinHeightBox T, (∑ r, ‖f r τ‖^2) ≤ B) :
    (∑ r, ‖∫ τ in mellinHeightBox T, w τ*f r τ‖^2) ≤
      (∫ τ, ‖w τ‖)^2*B := by
  have hc : Continuous (fun τ => WithLp.toLp 2 (fun r => f r τ)) :=
    (PiLp.continuous_toLp 2 (fun _ : κ => ℂ)).comp (continuous_pi hf)
  have ha : ∀ᵐ τ ∂(volume.restrict (mellinHeightBox T)), (∑ r, ‖f r τ‖^2) ≤ B := by
    filter_upwards [ae_restrict_mem (measurableSet_mellinHeightBox T)] with τ hτ
    exact hb τ hτ
  have hm := finite_row_integral_moment f w hc.aestronglyMeasurable hw.restrict hB ha
  apply hm.trans
  have hmass : (∫ τ in mellinHeightBox T, ‖w τ‖) ≤ ∫ τ, ‖w τ‖ :=
    setIntegral_le_integral hw.norm (Filter.Eventually.of_forall (fun _ => _root_.norm_nonneg _))
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (integral_nonneg (fun _ => _root_.norm_nonneg _)) hmass 2) hB

theorem independent_mellin_integral_moment (f : κ → (ι → ℝ) → ℂ)
    (hf : ∀ r, Continuous (f r)) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hW : ∀ i, HasCompactSupport (W i)) (hpos : ∀ i, tsupport (W i) ⊆ Ioi 0)
    (hsm : ∀ i, ContDiff ℝ ∞ (W i)) (hX : ∀ i, 0 < X i) (A : ℕ)
    {T L B : ℝ} (hT : 0 < T) (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hsize : ∀ r τ, ‖f r τ‖ ≤ L)
    (hbound : ∀ τ ∈ mellinHeightBox T, (∑ r, ‖f r τ‖^2) ≤ B) :
    (∑ r, ‖∫ τ, independentMellinWeight W X τ*f r τ‖^2) ≤
      2*(∏ i, zeroLineMellinMass (W i))^2*B+
        2*(Fintype.card κ:ℝ)*((L/T^A)*independentMellinMoment W A)^2 := by
  let w := independentMellinWeight W X
  have hw : Integrable w := independentMellinWeight_integrable W X hW hpos hsm hX
  have hc := finite_box_integral_moment f hf w hw T B hB hbound
  rw [independentMellinWeight_mass W X hX] at hc
  let H := (L/T^A)*independentMellinMoment W A
  have ht (r : κ) : ‖∫ τ in (mellinHeightBox T)ᶜ, w τ*f r τ‖ ≤ H := by
    calc
      _ ≤ L*(∫ τ in (mellinHeightBox T)ᶜ, ‖w τ‖) := by
        rw [← integral_const_mul]
        apply norm_integral_le_of_norm_le (hw.norm.restrict.const_mul L)
        filter_upwards with τ
        rw [norm_mul,mul_comm L]
        exact mul_le_mul_of_nonneg_left (hsize r τ) (_root_.norm_nonneg _)
      _ ≤ L*(independentMellinMoment W A/T^A) :=
        mul_le_mul_of_nonneg_left (independentMellinWeight_tail W X hW hpos hsm hX A hT) hL
      _ = H := by dsimp [H]; ring
  have ha (r : κ) :
      ‖(∫ τ, w τ*f r τ)-(∫ τ in mellinHeightBox T, w τ*f r τ)‖ ≤ H := by
    have hi : Integrable (fun τ => w τ*f r τ) := (hw.norm.mul_const L).mono'
      (hw.aestronglyMeasurable.mul (hf r).aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun τ => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hsize r τ) (_root_.norm_nonneg _)))
    rw [← integral_add_compl (measurableSet_mellinHeightBox T) hi,add_sub_cancel_left]
    exact ht r
  calc
    _ ≤ ∑ r, (2*‖∫ τ in mellinHeightBox T, w τ*f r τ‖^2+2*H^2) :=
      Finset.sum_le_sum (fun r _ => norm_square_le_central_tail _ _ (ha r))
    _ = 2*(∑ r, ‖∫ τ in mellinHeightBox T, w τ*f r τ‖^2)+2*(Fintype.card κ:ℝ)*H^2 := by
      rw [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      ring
    _ ≤ _ := by dsimp [H]; nlinarith

end CubicFirstMoment

end

end OAI
