import OAI.Probability.InvariantIsing.Magnetic.MagneticVariationalBounds
import OAI.Probability.InvariantIsing.Magnetic.MagneticFieldSymmetry

namespace OAI

/-! Rational approximation toward zero improves the constrained entropy.
This avoids a height-dependent continuity estimate for the magnetic profile. -/
noncomputable section
open Set
open scoped BigOperators
namespace InvariantIsing

lemma constrainedFieldValue_antitone_nonneg (h : FieldStep) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : t < 1) :
    constrainedFieldValue h t ≤ constrainedFieldValue h s := by
  have hs' : |s| < 1 := by rw [abs_of_nonneg hs]; exact hst.trans_lt ht
  have ht' : |t| ≤ 1 := by rw [abs_of_nonneg (hs.trans hst)]; exact ht.le
  have hb : 0 ≤ magneticBias h s := by
    apply (strictMono_fieldBiasMean h).le_iff_le.mp
    rw [fieldBiasMean_zero,fieldBiasMean_magneticBias h hs']
    exact hs
  have hh := constrainedFieldValue_bias_support h ht' (magneticBias_minimizes h hs')
  have hprod : 0 ≤ magneticBias h s*(t-s) := mul_nonneg hb (sub_nonneg.mpr hst)
  linarith

lemma constrainedFieldValue_abs (h : FieldStep) {s : ℝ} (hs : |s| < 1) :
    constrainedFieldValue h |s|=constrainedFieldValue h s := by
  rcases le_total 0 s with hp|hn
  · rw [abs_of_nonneg hp]
  · rw [abs_of_nonpos hn,constrainedFieldValue_even h hs]

lemma constrainedFieldValue_le_of_abs_le (h : FieldStep) {s t : ℝ}
    (ht : |t| < 1) (hst : |s| ≤ |t|) :
    constrainedFieldValue h t ≤ constrainedFieldValue h s := by
  rw [← constrainedFieldValue_abs h ht,← constrainedFieldValue_abs h (hst.trans_lt ht)]
  exact constrainedFieldValue_antitone_nonneg h (abs_nonneg _) hst ht

lemma exists_inward_rat_close {x δ : ℝ} (hx : |x| < 1) (hδ : 0 < δ) :
    ∃ q : ℚ, |(q:ℝ)| ≤ |x| ∧ |(q:ℝ)| < 1 ∧ |x-(q:ℝ)| < δ := by
  by_cases hz : x=0
  · subst x
    exact ⟨0,by simp,by norm_num,by simpa using hδ⟩
  have hp : 0 < |x| := abs_pos.mpr hz
  have hi : max 0 (|x|-δ) < |x| := max_lt hp (by linarith)
  obtain ⟨q,hq,hqx⟩ := exists_rat_btwn hi
  have hq0 : 0 < (q:ℝ) := (le_max_left _ _).trans_lt hq
  have hqd : |x|-(q:ℝ)<δ := by have := (le_max_right _ _).trans_lt hq; linarith
  by_cases hxp : 0 ≤ x
  · refine ⟨q,?_,?_,?_⟩
    · rw [abs_of_pos hq0]
      exact hqx.le
    · rw [abs_of_pos hq0]; exact hqx.trans hx
    · rw [abs_of_nonneg (by rw [abs_of_nonneg hxp] at hqx; linarith)]
      rwa [abs_of_nonneg hxp] at hqd
  · refine ⟨-q,?_,?_,?_⟩
    · simpa only [Rat.cast_neg,abs_neg,abs_of_pos hq0] using hqx.le
    · simpa only [Rat.cast_neg,abs_neg,abs_of_pos hq0] using hqx.trans hx
    · rw [Rat.cast_neg,abs_of_nonpos (by rw [abs_of_neg (lt_of_not_ge hxp)] at hqx; linarith)]
      rw [abs_of_neg (lt_of_not_ge hxp)] at hqd
      linarith

lemma magneticVariational_inward_mono {A : Type*} [Fintype A]
    (R : ℝ → ℝ) (γ s t : A → ℝ) (hγ : ∀ a, 0 ≤ γ a)
    (ht : ∀ a, |t a| < 1) (hst : ∀ a, |s a| ≤ |t a|) :
    magneticVariationalFunctional R γ t ≤ magneticVariationalFunctional R γ s := by
  apply iInf_mono
  intro p
  apply add_le_add _ le_rfl
  apply iSup_mono
  intro h
  apply EReal.coe_le_coe
  apply add_le_add _ le_rfl
  exact Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left
    (constrainedFieldValue_le_of_abs_le h (ht a) (hst a)) (hγ a))

end InvariantIsing

end

end OAI
