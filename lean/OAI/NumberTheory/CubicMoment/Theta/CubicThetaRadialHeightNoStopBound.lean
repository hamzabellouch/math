import OAI.NumberTheory.CubicMoment.Estimates.HeightNoStopBound
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialRestrictedNoStopWindow

namespace OAI

/-! Propagate the constructed radial transform through the literal tail.
No radial normalization or Voronoi premise is used. -/
noncomputable section
open Filter Asymptotics
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem cubicTheta_radial_height_noStop_bound (hpnt : PrimaryPrimePNT)
    {γ : Type*} {W : γ → ℝ → ℂ} (hW : UniformLogWeights W)
    {MV : ℝ} (hMV : MontgomeryVaughanBound MV) (hMean0 : 0 ≤ MV)
    {κ η A cap : ℝ} (hκ : 0 < κ) (hκsmall : κ < 1/3) (hη : η ≤ κ/4)
    (hA : 0 ≤ A) (hcap : 1 < cap) (M : ℕ) :
    ∃ ρ C E : ℝ, 1 < ρ ∧ ρ ≤ 2 ∧ ρ ≤ cap ∧ 0 ≤ C ∧ 0 ≤ E ∧
      ∀ᶠ X : ℝ in atTop, ∀ (i : γ) (R : Finset Eisenstein)
        (v : Eisenstein → ℂ) (ψ : ℝ → ℝ) (w H T X₀ : ℝ)
        (P : Eisenstein → Eisenstein → Prop),
      Real.log X ≤ T → T ≤ X^(1/6+η) → 0 < H → 0 < X₀ →
      (∀ r ∈ R, primary r) → (∀ r ∈ R, ‖v r‖ ≤ A) →
      (∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) →
      ‖restrictedNoStopGaussWindowValue R v ψ w ρ (heightNoStopThreshold κ X T)
        (Real.exp hW.radius) 0 (W i) H T X X₀ P‖ ≤
        (1+Real.log X)*(C*X^(5/6-min (1/100) (3*κ/16))+
          E*X^(5/6:ℝ)/(Real.log X)^M) := by
  let ν := min (1/100:ℝ) κ
  have hν : 0 < ν := lt_min (by norm_num) hκ
  obtain ⟨ρ,C,E,hρ,hρ₂,hsmall,hC,hE,hbound⟩ := cubicTheta_radial_restricted_noStop_window_bound
    hpnt hW hMV hMean0 hκ hη hν hA hcap M
  refine ⟨ρ,C,E,hρ,hρ₂,hsmall,hC,hE,?_⟩
  filter_upwards [hbound,eventually_height_noStop_window_scales hW hκ hκsmall,
    eventually_ge_atTop (2:ℝ),Real.tendsto_log_atTop.eventually_ge_atTop 1]
    with X hb hs hX hlog
  intro i R v ψ w H T X₀ P hLT hT hH hX₀ hR hv hψ
  have hX1 : 1 ≤ X := by linarith
  have hF1 : 1 ≤ Real.exp hW.radius*X :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_exp hW.radius_nonneg) hX1
  obtain ⟨hY,hdist,hrange⟩ := hs T hT
  have hνle : ν/4 ≤ (if T ≤ X^(1/100:ℝ) then 1/100 else κ)/4 := by
    dsimp only [ν]
    split_ifs
    · linarith [min_le_left (1/100:ℝ) κ]
    · linarith [min_le_right (1/100:ℝ) κ]
  have hz : 0 ≤ heightNoStopThreshold κ X T := by
    unfold heightNoStopThreshold
    split_ifs <;> positivity
  have hdist' : (Real.exp hW.radius*X)^(ν/4)*heightNoStopThreshold κ X T ≤
      heightNoStopOuterBound κ X T :=
    (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hF1 hνle) hz).trans hdist
  have hYX : heightNoStopOuterBound κ X T ≤ X := by
    have hhi : 2*heightNoStopOuterBound κ X T ≤ X := by
      rcases hrange with h | h
      · exact h.1.trans (by simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num : (2/5:ℝ) ≤ 1))
      · exact h.1.trans (by simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le hX1 (show 1/3-κ/2 ≤ 1 by linarith))
    linarith
  have hlogs : 1+Real.log (heightNoStopOuterBound κ X T) ≤ 1+Real.log X :=
    add_le_add le_rfl (Real.log_le_log (zero_lt_one.trans_le hY) hYX)
  have he := hb i R v ψ w (heightNoStopThreshold κ X T)
    (heightNoStopOuterBound κ X T) H T X₀ P hX hlog hY hLT hH hX₀ hdist' hrange hR hv hψ
  exact he.trans (mul_le_mul_of_nonneg_right hlogs (by positivity))

end CubicFirstMoment

end

end OAI
