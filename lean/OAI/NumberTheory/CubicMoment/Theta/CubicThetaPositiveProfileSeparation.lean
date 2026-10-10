import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPositiveGramDiagonal

namespace OAI

/-! Reciprocal height separation removes every nonidentity row from a
mixed positive-cutoff Gram pairing. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

lemma CubicThetaBottomRow.height_product_le_one (r : CubicThetaBottomRow)
    (hr : r≠cubicThetaZeroRow) {p : ℂ × ℝ} (hp : 0<p.2) :
    r.height p*p.2≤1 := by
  have hc : r.completion.val 1 0≠0 := by
    have he := congrArg CubicThetaBottomRow.c r.completion_row
    change r.completion.val 1 0=r.c at he
    rw [he]
    exact fun hz => hr ((CubicThetaBottomRow.c_zero_iff r).mp hz)
  have he := cubicThetaMobius_height_product_le r.completion.val hc hp
  change (cubicThetaBottomRow r.completion).height p*p.2≤1 at he
  rwa [r.completion_row] at he

lemma cubicThetaPositiveFourierProfile_separated (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {δ : ℝ} (hW : ∀ v≤δ,W v=0) {p : ℂ × ℝ} (hp : 0<p.2) (hsep : 1≤δ*p.2) :
    cubicThetaFourierProfileSeries h p W=W p.2*cubicThetaHorizontalCharacter h p.1 := by
  have he : cubicThetaFourierProfileSeries h p W=
      cubicThetaFourierProfileTerm h cubicThetaZeroRow p W := by
    apply tsum_eq_single
    intro r hr
    apply cubicThetaFourierProfileTerm_zero
    apply hW
    by_contra hn
    have hm := mul_lt_mul_of_pos_right (lt_of_not_ge hn) hp
    have hb := r.height_product_le_one hr hp
    linarith
  rw [he]
  exact cubicThetaFourierProfileTerm_zeroRow h W hp

theorem cubicThetaPositiveProfileGram_separated (h k : Eisenstein)
    (W V : C_c(ℝ,ℂ)) {ε δ : ℝ} (hε : 0<ε) (hδ : 0<δ)
    (hW : ∀ v≤ε,W v=0) (hV : ∀ v≤δ,V v=0) (hsep : 1≤ε*δ) :
    inner ℂ (cubicThetaPositiveFourierProfileL2 h W hε hW)
      (cubicThetaPositiveFourierProfileL2 k V hδ hV)=
      ∫ v in Ioi ε,star (W v)*V v/(v:ℂ)^3*
        cubicThetaHorizontalFourierCoefficient h (cubicThetaHorizontalCharacter k) := by
  rw [cubicThetaPositiveProfileGram_unfold h k W V hε hδ hW hV,
    ←cubicThetaPositiveProfileGram_zeroRow h k W V hε hW]
  apply integral_congr_ae
  filter_upwards with p
  by_cases hz : cubicThetaFourierStripSeed h W p=0
  · simp only [hz,star_zero,zero_mul]
  · have hv : ε<p.val.2 := by
      by_contra hn
      have hw := hW p.val.2 (le_of_not_gt hn)
      apply hz
      simp only [cubicThetaFourierStripSeed,hw,zero_mul,ite_self]
    have hs : 1≤δ*p.val.2 := by
      have hm := mul_le_mul_of_nonneg_left hv.le hδ.le
      nlinarith
    rw [cubicThetaPositiveFourierProfile_separated k V hV p.property hs,
      cubicThetaFourierProfileTerm_zeroRow k V p.property]

end CubicFirstMoment

end

end OAI
