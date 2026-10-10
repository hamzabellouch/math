import OAI.Analysis.BackwardIntertwiners.ConvolutionBounds

namespace OAI

namespace BackwardIntertwiners
open Filter
open scoped Topology
noncomputable section


def coefficientObstacle (d : ℕ → ℂ) : Set ℕ := {n | 0 < n ∧ d n ≠ 0}

def coefficientEnvelope (d : ℕ → ℂ) : ℕ → ℝ :=
  convexEnvelope (coefficientObstacle d) (fun n => -Real.log ‖d n‖)

namespace CoefficientEnvelope

variable {d : ℕ → ℂ} {G : ℕ → ℝ}
variable (hu : ∀ n : ℕ, ∃ k, n < k ∧ d k ≠ 0)
variable (hG : DiscreteConvex G) (hG0 : G 0 = 0)
variable (hb : ∀ n, ‖d n‖ ≤ Real.exp (-G n))

include hu in
lemma unbounded : ∀ n : ℕ, ∃ k, n < k ∧ k ∈ coefficientObstacle d := by
  intro n
  obtain ⟨k, hk, hd⟩ := hu n
  exact ⟨k, hk, by exact ⟨by omega, hd⟩⟩

include hG hG0 hb in
lemma minorant : G ∈ convexMinorants (coefficientObstacle d) (fun n => -Real.log ‖d n‖) := by
  refine ⟨hG0, hG, ?_⟩
  intro n hn
  have hn0 : 0 < ‖d n‖ := norm_pos_iff.mpr hn.2
  have hh := Real.log_le_log hn0 (hb n)
  rw [Real.log_exp] at hh
  linarith

include hu hG hG0 hb in
lemma properties :
    coefficientEnvelope d 0 = 0 ∧ DiscreteConvex (coefficientEnvelope d) ∧
    (∀ n, G n ≤ coefficientEnvelope d n) ∧
    (∀ n, ‖d n‖ ≤ Real.exp (-coefficientEnvelope d n)) ∧
    (∀ n, 0 < coefficientEnvelope d (n+2) - 2*coefficientEnvelope d (n+1) +
      coefficientEnvelope d n → ‖d (n+1)‖ = Real.exp (-coefficientEnvelope d (n+1))) := by
  have hm := minorant hG hG0 hb
  have he : (convexMinorants (coefficientObstacle d) (fun n => -Real.log ‖d n‖)).Nonempty := ⟨G, hm⟩
  have hU := unbounded hu
  refine ⟨ConvexEnvelope.zero hU he, ConvexEnvelope.convex hU he,
    ConvexEnvelope.le_envelope hU hm, ?_, ?_⟩
  · intro n
    by_cases hn : n = 0
    · subst n
      simpa only [coefficientEnvelope, ConvexEnvelope.zero hU he, hG0] using hb 0
    · by_cases hd : d n = 0
      · simp only [hd, norm_zero]; exact (Real.exp_pos _).le
      · have hbelow := ConvexEnvelope.below he (show n ∈ coefficientObstacle d from ⟨by omega, hd⟩)
        have hlog : Real.log ‖d n‖ ≤ -coefficientEnvelope d n := by
          change coefficientEnvelope d n ≤ -Real.log ‖d n‖ at hbelow
          linarith
        simpa only [Real.exp_log (norm_pos_iff.mpr hd)] using Real.exp_le_exp.mpr hlog
  · intro n hn
    obtain ⟨hd, hc⟩ := ConvexEnvelope.contact hU he n hn
    change coefficientEnvelope d (n+1) = -Real.log ‖d (n+1)‖ at hc
    rw [hc, neg_neg, Real.exp_log (norm_pos_iff.mpr hd.2)]

end CoefficientEnvelope



theorem no_both_unbounded {P Q : ℕ → ℝ} {b c : ℤ → ℂ}
    (hb : EnvelopeBounds P Q b c) (hP : DiscreteConvex P) (hQ : DiscreteConvex Q)
    (hP0 : P 0 = 0) (hQ0 : Q 0 = 0) {lam δ : ℝ}
    (hlam : Real.log 3 < lam) (hδ : lam < δ)
    (hqp : ∀ᶠ n : ℕ in atTop, δ*(n : ℝ)^2 ≤ P n)
    (hqq : ∀ᶠ n : ℕ in atTop, δ*(n : ℝ)^2 ≤ Q n)
    (hbu : ∀ n : ℕ, ∃ k, n < k ∧ b (k : ℤ) ≠ 0)
    (hcu : ∀ n : ℕ, ∃ k, n < k ∧ c (-(k : ℤ)) ≠ 0)
    (hz : ∀ r : ℕ, 1 ≤ r → (∑' j : ℤ, b j * c (j-r)) = 0) : False := by
  obtain ⟨hA0, hA, hPA, hcA, hcontactA⟩ :=
    CoefficientEnvelope.properties hcu hP hP0 hb.c_neg
  obtain ⟨hB0, hB, hQB, hbB, hcontactB⟩ :=
    CoefficientEnvelope.properties hbu hQ hQ0 hb.b_pos
  let A := coefficientEnvelope (fun n => c (-(n : ℤ)))
  let B := coefficientEnvelope (fun n => b (n : ℤ))
  apply no_correlation_of_envelopes (A := A) (B := B) (b := b) (c := c)
    ?_ hA hB hA0 hB0 hlam hδ ?_ ?_ hcontactA hcontactB hz
  · refine ⟨hbB, ?_, ?_, hcA⟩
    · intro n
      exact (hb.b_neg n).trans (Real.exp_le_exp.mpr (hPA n))
    · intro n
      exact (hb.c_pos n).trans (Real.exp_le_exp.mpr (hQB n))
  · filter_upwards [hqp] with n hn using hn.trans (hPA n)
  · filter_upwards [hqq] with n hn using hn.trans (hQB n)


def boundedSideTail (B : ℕ → ℝ) (c : ℤ → ℂ) (h : ℤ) (p k : ℕ) : ℝ :=
  Real.exp (B p - B (p+k+1)) * ‖c (h+(k:ℤ)+1)‖

lemma boundedSideTail_nonneg (B : ℕ → ℝ) (c : ℤ → ℂ) (h : ℤ) (p k : ℕ) :
    0 ≤ boundedSideTail B c h p k := mul_nonneg (Real.exp_pos _).le (norm_nonneg _)

lemma boundedSideTail_mono {B : ℕ → ℝ} (hB : DiscreteConvex B)
    (c : ℤ → ℂ) (h : ℤ) {p₀ p : ℕ} (hpp : p₀ ≤ p) (k : ℕ) :
    boundedSideTail B c h p k ≤ boundedSideTail B c h p₀ k := by
  have hh := hB.increment_mono hpp (k+1)
  unfold boundedSideTail
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  simp only [← Nat.add_assoc] at hh
  linarith

lemma boundedSideTail_tendsto {B : ℕ → ℝ} (hB : DiscreteConvex B)
    (hs : Tendsto (fun n => B (n+1)-B n) atTop atTop)
    (c : ℤ → ℂ) (h : ℤ) {p₀ : ℕ} (hsum : Summable (boundedSideTail B c h p₀)) :
    Tendsto (fun p => ∑' k, boundedSideTail B c h p k) atTop (𝓝 0) := by
  have hpoint (k : ℕ) : Tendsto (fun p => boundedSideTail B c h p k) atTop (𝓝 0) := by
    have heq : (fun p => boundedSideTail B c h p k) =
        (fun p => normalizedTailTerm B p k * (Real.exp (-B (k+1)) * ‖c (h+(k:ℤ)+1)‖)) := by
      funext p
      unfold boundedSideTail normalizedTailTerm
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      ring
    rw [heq]
    simpa using (hB.tail_term_tendsto hs k).mul_const
      (Real.exp (-B (k+1)) * ‖c (h+(k:ℤ)+1)‖)
  have ht := tendsto_tsum_of_dominated_convergence hsum hpoint
    (show ∀ᶠ p : ℕ in atTop, ∀ k,
      ‖boundedSideTail B c h p k‖ ≤ boundedSideTail B c h p₀ k from ?_)
  · simpa using ht
  · filter_upwards [eventually_ge_atTop p₀] with p hp k
    rw [Real.norm_eq_abs, abs_of_nonneg (boundedSideTail_nonneg _ _ _ _ _)]
    exact boundedSideTail_mono hB c h hp k



theorem no_unbounded_against_min {B : ℕ → ℝ} {b c : ℤ → ℂ}
    (hB : DiscreteConvex B) (hB0 : B 0 = 0) {δ : ℝ} (hδ : 0 < δ)
    (hquad : ∀ᶠ n : ℕ in atTop, δ*(n:ℝ)^2 ≤ B n)
    (hb : ∀ n : ℕ, ‖b n‖ ≤ Real.exp (-B n))
    (hc : ∀ n, 0 < B (n+2) - 2*B (n+1) + B n →
      ‖b ((n+1:ℕ):ℤ)‖ = Real.exp (-B (n+1)))
    {h : ℤ} (hch : c h ≠ 0) (hcmin : ∀ j : ℤ, j < h → c j = 0)
    {p₀ : ℕ} (hsum : Summable (boundedSideTail B c h p₀))
    (hz : ∀ r : ℕ, 1 ≤ r → (∑' j : ℤ, b j * c (j-r)) = 0) : False := by
  have hchpos := norm_pos_iff.mpr hch
  have ht := boundedSideTail_tendsto hB (hB.slopes_tendsto hB0 hδ hquad) c h hsum
  obtain ⟨N, hN⟩ := eventually_atTop.1 (ht (eventually_lt_nhds hchpos))
  obtain ⟨n, hn, hcurv⟩ := large_curvature hδ hδ hquad (max N (max p₀ (h.toNat+1)))
  let p := n+1
  have hp₀ : p₀ ≤ p := by dsimp [p]; omega
  have hpN : N ≤ p := by dsimp [p]; omega
  have hph : h < (p : ℤ) := by dsimp [p]; omega
  have hcontact : ‖b (p : ℤ)‖ = Real.exp (-B p) := hc n (by simpa using hcurv)
  have htailsum : Summable (boundedSideTail B c h p) := by
    apply hsum.of_norm_bounded
    intro k
    rw [Real.norm_eq_abs, abs_of_nonneg (boundedSideTail_nonneg _ _ _ _ _)]
    exact boundedSideTail_mono hB c h hp₀ k
  let f := fun i : ℤ => b ((p:ℤ)+i) * c (h+i)
  have hfneg : ∀ k : ℕ, f (-((k:ℤ)+1)) = 0 := by
    intro k
    dsimp [f]
    rw [hcmin _ (by omega), mul_zero]
  have hfbound (k : ℕ) : ‖f ((k:ℤ)+1)‖ ≤ Real.exp (-B p) * boundedSideTail B c h p k := by
    dsimp [f, boundedSideTail]
    rw [norm_mul, ← mul_assoc, ← Real.exp_add]
    have he : -B p + (B p - B (p+k+1)) = -B (p+k+1) := by ring
    rw [he]
    have hi : (p:ℤ)+((k:ℤ)+1) = ((p+k+1:ℕ):ℤ) := by omega
    rw [hi]
    simpa only [add_assoc] using mul_le_mul_of_nonneg_right (hb (p+k+1)) (norm_nonneg (c (h+(k:ℤ)+1)))
  have hfpos : Summable (fun k : ℕ => ‖f ((k:ℤ)+1)‖) := by
    apply (htailsum.mul_left (Real.exp (-B p))).of_norm_bounded
    intro k
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hfbound k
  have hfn : Summable (fun k : ℕ => ‖f (-((k:ℤ)+1))‖) := by
    simp only [hfneg, norm_zero]
    exact summable_zero
  have hzcenter : (∑' i : ℤ, f i) = 0 := by
    let r := ((p:ℤ)-h).toNat
    have hr : 1 ≤ r := by dsimp [r]; omega
    have hri : (r:ℤ) = (p:ℤ)-h := by dsimp [r]; omega
    calc (∑' i : ℤ, f i) = ∑' i : ℤ, b ((p:ℤ)+i) * c (((p:ℤ)+i)-(r:ℤ)) := by
          apply tsum_congr
          intro i
          dsimp [f]
          congr 2
          omega
      _ = ∑' j : ℤ, b j * c (j-r) := by
          simpa only [Equiv.coe_addLeft] using
            (Equiv.addLeft (p:ℤ)).tsum_eq (fun j : ℤ => b j * c (j-r))
      _ = 0 := hz r hr
  have hcentral := central_norm_le_of_correlation_zero f hfpos hfn hzcenter
  simp only [hfneg, norm_zero, tsum_zero, add_zero] at hcentral
  have hcentral' : Real.exp (-B p) * ‖c h‖ ≤
      Real.exp (-B p) * ∑' k, boundedSideTail B c h p k := by
    calc Real.exp (-B p) * ‖c h‖ = ‖f 0‖ := by simp [f, hcontact]
      _ ≤ ∑' k : ℕ, ‖f ((k:ℤ)+1)‖ := hcentral
      _ ≤ ∑' k, Real.exp (-B p) * boundedSideTail B c h p k :=
        hfpos.tsum_le_tsum hfbound (htailsum.mul_left _)
      _ = _ := tsum_mul_left
  have hle := (mul_le_mul_iff_right₀ (Real.exp_pos (-B p))).mp hcentral'
  exact (not_lt_of_ge hle) (hN p hpN)


def positiveLog (w : ℤ → ℝ) (n : ℕ) : ℝ := -Real.log (w n)
def negativeLog (w : ℤ → ℝ) (n : ℕ) : ℝ := Real.log (w (-(n:ℤ)))
def stepRatio (w : ℤ → ℝ) (j : ℤ) : ℝ := w (j+1) / w j

lemma stepRatio_summable {w : ℤ → ℝ} (hw : ∀ j, 0 < w j) (hw0 : w 0 = 1)
    (hP : DiscreteConvex (negativeLog w)) (hQ : DiscreteConvex (positiveLog w))
    {δ : ℝ} (hδ : 0 < δ)
    (hqp : ∀ᶠ n : ℕ in atTop, δ*(n:ℝ)^2 ≤ negativeLog w n)
    (hqq : ∀ᶠ n : ℕ in atTop, δ*(n:ℝ)^2 ≤ positiveLog w n) :
    Summable (stepRatio w) := by
  have hP0 : negativeLog w 0 = 0 := by simp [negativeLog, hw0]
  have hQ0 : positiveLog w 0 = 0 := by simp [positiveLog, hw0]
  have hsP := hP.summable_exp_neg_slope hP0 hδ hqp
  have hsQ := hQ.summable_exp_neg_slope hQ0 hδ hqq
  apply Summable.of_nat_of_neg_add_one
  · apply hsQ.congr
    intro n
    unfold stepRatio positiveLog
    have he : -(-Real.log (w (n+1)) - -Real.log (w n)) =
        Real.log (w (n+1)) - Real.log (w n) := by ring
    push_cast
    rw [he, Real.exp_sub, Real.exp_log (hw _), Real.exp_log (hw _)]
  · apply hsP.congr
    intro n
    unfold stepRatio negativeLog
    have hi : -((n:ℤ)+1)+1 = -(n:ℤ) := by omega
    rw [hi]
    push_cast
    rw [neg_sub, Real.exp_sub, Real.exp_log (hw _), Real.exp_log (hw _)]

lemma bounds_of_weight {w : ℤ → ℝ} (hw : ∀ j, 0 < w j) {b c : ℤ → ℂ}
    (hb : ∀ j, ‖b j‖ ≤ w j) (hc : ∀ j, ‖c j‖ * w j ≤ 1) :
    EnvelopeBounds (negativeLog w) (positiveLog w) b c := by
  have hc' (j : ℤ) : ‖c j‖ ≤ (w j)⁻¹ := by
    simpa only [one_div] using (le_div_iff₀ (hw j)).mpr (hc j)
  constructor
  · intro n
    simpa [positiveLog, Real.exp_log (hw _)] using hb n
  · intro n
    simpa [negativeLog, Real.exp_log (hw _)] using hb (-(n:ℤ))
  · intro n
    simpa [positiveLog, Real.exp_neg, Real.exp_log (hw _)] using hc' n
  · intro n
    simpa [negativeLog, Real.exp_neg, Real.exp_log (hw _)] using hc' (-(n:ℤ))

lemma boundedSideTail_summable {w : ℤ → ℝ} (hw : ∀ j, 0 < w j)
    (hdec : Antitone w) (hs : Summable (stepRatio w))
    {B : ℕ → ℝ} (hBw : ∀ n : ℕ, Real.exp (-B n) ≤ w n)
    {c : ℤ → ℂ} (hc : ∀ j, ‖c j‖ * w j ≤ 1)
    (h : ℤ) {p₀ : ℕ} (hp₀ : h+1 ≤ (p₀:ℤ)) :
    Summable (boundedSideTail B c h p₀) := by
  have hsm := hs.comp_injective (i := fun k : ℕ => h+(k:ℤ)+1) (by
    intro a b hab; dsimp only at hab; omega)
  apply (hsm.mul_left (Real.exp (B p₀))).of_norm_bounded
  intro k
  rw [Real.norm_eq_abs, abs_of_nonneg (boundedSideTail_nonneg _ _ _ _ _)]
  change boundedSideTail B c h p₀ k ≤ Real.exp (B p₀) * stepRatio w (h+(k:ℤ)+1)
  have hwle : Real.exp (-B (p₀+k+1)) ≤ w (h+(k:ℤ)+1+1) := by
    exact (hBw _).trans (hdec (by omega))
  have hcw : ‖c (h+(k:ℤ)+1)‖ ≤ 1 / w (h+(k:ℤ)+1) :=
    (le_div_iff₀ (hw _)).mpr (hc _)
  unfold boundedSideTail stepRatio
  rw [Real.exp_sub, div_eq_mul_inv, ← Real.exp_neg, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  calc Real.exp (-B (p₀+k+1)) * ‖c (h+(k:ℤ)+1)‖ ≤
      w (h+(k:ℤ)+1+1) * (1 / w (h+(k:ℤ)+1)) :=
        mul_le_mul hwle hcw (norm_nonneg _) (hw _).le
    _ = _ := by ring

lemma nat_support_unbounded {d : ℤ → ℂ}
    (hu : ¬∃ m : ℤ, ∀ j : ℤ, d j ≠ 0 → j ≤ m) :
    ∀ n : ℕ, ∃ k, n < k ∧ d (k:ℤ) ≠ 0 := by
  push Not at hu
  intro n
  obtain ⟨j, hd, hj⟩ := hu n
  refine ⟨j.toNat, by omega, ?_⟩
  have he : (j.toNat:ℤ) = j := by omega
  simpa only [he] using hd



lemma bounded_above_of_min {w : ℤ → ℝ} (hw : ∀ j, 0 < w j)
    (hdec : Antitone w) (hw0 : w 0 = 1) (hs : Summable (stepRatio w))
    (hQ : DiscreteConvex (positiveLog w)) {δ : ℝ} (hδ : 0 < δ)
    (hqq : ∀ᶠ n : ℕ in atTop, δ*(n:ℝ)^2 ≤ positiveLog w n)
    {b c : ℤ → ℂ} (hb : ∀ j, ‖b j‖ ≤ w j) (hc : ∀ j, ‖c j‖*w j ≤ 1)
    {h : ℤ} (hch : c h ≠ 0) (hcmin : ∀ j : ℤ, j < h → c j = 0)
    (hz : ∀ r : ℕ, 1 ≤ r → (∑' j : ℤ, b j * c (j-r)) = 0) :
    ∃ m : ℤ, ∀ j : ℤ, b j ≠ 0 → j ≤ m := by
  by_contra hu
  have hbu := nat_support_unbounded hu
  have hQ0 : positiveLog w 0 = 0 := by simp [positiveLog, hw0]
  obtain ⟨hB0, hB, hQB, hbB, hcontactB⟩ :=
    CoefficientEnvelope.properties hbu hQ hQ0 (bounds_of_weight hw hb hc).b_pos
  let B := coefficientEnvelope (fun n => b (n:ℤ))
  have hquad : ∀ᶠ n : ℕ in atTop, δ*(n:ℝ)^2 ≤ B n := by
    filter_upwards [hqq] with n hn using hn.trans (hQB n)
  have hBw (n : ℕ) : Real.exp (-B n) ≤ w n := by
    have hh := Real.exp_le_exp.mpr (neg_le_neg (hQB n))
    simpa only [positiveLog, neg_neg, Real.exp_log (hw _)] using hh
  exact no_unbounded_against_min hB hB0 hδ hquad hbB hcontactB hch hcmin
    (boundedSideTail_summable hw hdec hs hBw hc h (p₀ := h.toNat+1) (by omega)) hz


end
end BackwardIntertwiners

end OAI
