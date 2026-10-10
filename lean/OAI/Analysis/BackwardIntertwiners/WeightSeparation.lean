import OAI.Analysis.BackwardIntertwiners.CoefficientSupport

namespace OAI

namespace BackwardIntertwiners
open Filter
open scoped Topology
noncomputable section


structure QuadraticWeights (w : ℤ → ℝ) : Prop where
  positive : ∀ j, 0 < w j
  decreasing : Antitone w
  convex_negative : DiscreteConvex (fun n => Real.log (w (-(n : ℤ))))
  concave_positive : DiscreteConvex (fun n => -Real.log (w n))
  root_sum : Summable (fun j : ℤ => if j = 0 then 0 else w j ^ (1 / (j : ℝ)))
  quadratic : ∃ a : ℝ, Real.log 3 < a ∧
    Tendsto (fun n : ℕ => Real.log (w n) / (n : ℝ)^2) atTop (𝓝 (-a)) ∧
    Tendsto (fun n : ℕ => Real.log (w (-(n : ℤ))) / (n : ℝ)^2) atTop (𝓝 a)


def SupportSeparation (w : ℤ → ℝ) : Prop :=
  ∀ b c : ℤ → ℂ,
    (∃ j, b j ≠ 0) → (∃ j, c j ≠ 0) →
    (∀ j, ‖b j‖ ≤ w j) → (∀ j, ‖c j‖ * w j ≤ 1) →
    (∀ r : ℕ, 1 ≤ r → (∑' j : ℤ, b j * c (j - r)) = 0) →
    ∃ t h : ℤ, b t ≠ 0 ∧ c h ≠ 0 ∧
      (∀ j, t < j → b j = 0) ∧ (∀ j, j < h → c j = 0) ∧ t ≤ h

def reflectedWeight (w : ℤ → ℝ) (j : ℤ) : ℝ := (w (-j))⁻¹

lemma reflectedWeight_pos {w : ℤ → ℝ} (hw : ∀ j, 0 < w j) (j : ℤ) :
    0 < reflectedWeight w j := inv_pos.mpr (hw _)

lemma reflectedWeight_antitone {w : ℤ → ℝ} (hw : ∀ j, 0 < w j) (hdec : Antitone w) :
    Antitone (reflectedWeight w) := by
  intro i j hij
  exact (inv_le_inv₀ (hw _) (hw _)).mpr (hdec (neg_le_neg hij))

lemma reflected_positiveLog (w : ℤ → ℝ) : positiveLog (reflectedWeight w) = negativeLog w := by
  funext n
  simp [positiveLog, negativeLog, reflectedWeight, Real.log_inv]

lemma reflected_negativeLog (w : ℤ → ℝ) : negativeLog (reflectedWeight w) = positiveLog w := by
  funext n
  simp [positiveLog, negativeLog, reflectedWeight, Real.log_inv]

lemma reflected_stepRatio_summable {w : ℤ → ℝ} (hs : Summable (stepRatio w)) :
    Summable (stepRatio (reflectedWeight w)) := by
  have hh := hs.comp_injective (i := fun j : ℤ => -j-1) (by
    intro a b hab; dsimp only at hab; omega)
  apply hh.congr
  intro j
  dsimp [stepRatio, reflectedWeight]
  have e₁ : -j-1+1 = -j := by omega
  have e₂ : -(j+1) = -j-1 := by omega
  rw [e₁, e₂, inv_div_inv]

lemma reflected_correlations {b c : ℤ → ℂ}
    (hz : ∀ r : ℕ, 1 ≤ r → (∑' j : ℤ, b j * c (j-r)) = 0) :
    ∀ r : ℕ, 1 ≤ r → (∑' j : ℤ, c (-j) * b (-(j-r))) = 0 := by
  intro r hr
  let e : ℤ ≃ ℤ := ⟨fun j => (r:ℤ)-j, fun j => (r:ℤ)-j, by intro j; dsimp only; omega, by intro j; dsimp only; omega⟩
  calc (∑' j : ℤ, c (-j) * b (-(j-r))) =
      ∑' j : ℤ, b (e j) * c (e j-r) := by
        apply tsum_congr
        intro j
        dsimp [e]
        have e₁ : (r:ℤ)-j = -(j-r) := by omega
        have e₂ : (r:ℤ)-j-r = -j := by omega
        rw [e₁, show -(j-(r:ℤ))-(r:ℤ) = -j by omega, mul_comm]
    _ = ∑' j : ℤ, b j * c (j-r) := e.tsum_eq (fun j : ℤ => b j * c (j-r))
    _ = 0 := hz r hr

lemma reflected_bounds {w : ℤ → ℝ} (hw : ∀ j, 0 < w j) {b c : ℤ → ℂ}
    (hb : ∀ j, ‖b j‖ ≤ w j) (hc : ∀ j, ‖c j‖*w j ≤ 1) :
    (∀ j, ‖c (-j)‖ ≤ reflectedWeight w j) ∧
    (∀ j, ‖b (-j)‖*reflectedWeight w j ≤ 1) := by
  constructor
  · intro j
    simpa only [reflectedWeight, one_div] using (le_div_iff₀ (hw (-j))).mpr (hc (-j))
  · intro j
    dsimp [reflectedWeight]
    rw [← div_eq_mul_inv]
    exact (div_le_one (hw _)).mpr (hb _)



theorem normalized_support_separation {w : ℤ → ℝ} (hw : ∀ j, 0 < w j)
    (hdec : Antitone w) (hw0 : w 0 = 1)
    (hP : DiscreteConvex (negativeLog w)) (hQ : DiscreteConvex (positiveLog w))
    {lam δ : ℝ} (hlam : Real.log 3 < lam) (hδ : lam < δ)
    (hqp : ∀ᶠ n : ℕ in atTop, δ*(n:ℝ)^2 ≤ negativeLog w n)
    (hqq : ∀ᶠ n : ℕ in atTop, δ*(n:ℝ)^2 ≤ positiveLog w n) :
    SupportSeparation w := by
  intro b c hbn hcn hb hc hz
  have hδ0 : 0 < δ := lt_trans (lt_trans (Real.log_pos (by norm_num : (1:ℝ)<3)) hlam) hδ
  have hP0 : negativeLog w 0 = 0 := by simp [negativeLog, hw0]
  have hQ0 : positiveLog w 0 = 0 := by simp [positiveLog, hw0]
  have hs := stepRatio_summable hw hw0 hP hQ hδ0 hqp hqq
  have hb_bd : ∃ m : ℤ, ∀ j : ℤ, b j ≠ 0 → j ≤ m := by
    by_cases hc_bd : ∃ m : ℤ, ∀ j : ℤ, c j ≠ 0 → m ≤ j
    · obtain ⟨h, hch, hh⟩ := Int.exists_least_of_bdd hc_bd hcn
      apply bounded_above_of_min hw hdec hw0 hs hQ hδ0 hqq hb hc hch ?_ hz
      intro j hj
      by_contra hne
      have := hh j hne
      omega
    · by_contra hbu
      have hcu : ¬∃ m : ℤ, ∀ j : ℤ, c (-j) ≠ 0 → j ≤ m := by
        rintro ⟨m, hm⟩
        apply hc_bd
        refine ⟨-m, ?_⟩
        intro j hj
        have hh := hm (-j) (by simpa using hj)
        omega
      exact no_both_unbounded (bounds_of_weight hw hb hc) hP hQ hP0 hQ0 hlam hδ hqp hqq
        (nat_support_unbounded hbu) (nat_support_unbounded hcu) hz
  obtain ⟨t, hbt, ht⟩ := Int.exists_greatest_of_bdd hb_bd hbn
  have hc_bd : ∃ m : ℤ, ∀ j : ℤ, c j ≠ 0 → m ≤ j := by
    have hwr0 : reflectedWeight w 0 = 1 := by simp [reflectedWeight, hw0]
    have hQr : DiscreteConvex (positiveLog (reflectedWeight w)) := by
      rw [reflected_positiveLog]; exact hP
    have hqpr : ∀ᶠ n : ℕ in atTop, δ*(n:ℝ)^2 ≤ positiveLog (reflectedWeight w) n := by
      simpa only [reflected_positiveLog] using hqp
    obtain ⟨hbr, hcr⟩ := reflected_bounds hw hb hc
    have hzref := reflected_correlations hz
    have hm := bounded_above_of_min (reflectedWeight_pos hw) (reflectedWeight_antitone hw hdec)
      hwr0 (reflected_stepRatio_summable hs) hQr hδ0 hqpr hbr hcr
      (h := -t) (by simpa using hbt) (by
        intro j hj
        by_contra hne
        have hh := ht (-j) hne
        omega) hzref
    obtain ⟨m, hm⟩ := hm
    refine ⟨-m, ?_⟩
    intro j hj
    have hh := hm (-j) (by simpa using hj)
    omega
  obtain ⟨h, hch, hh⟩ := Int.exists_least_of_bdd hc_bd hcn
  have hbmax : ∀ j : ℤ, t < j → b j = 0 := by
    intro j hj
    by_contra hne
    have := ht j hne
    omega
  have hcmin : ∀ j : ℤ, j < h → c j = 0 := by
    intro j hj
    by_contra hne
    have := hh j hne
    omega
  refine ⟨t, h, hbt, hch, hbmax, hcmin, ?_⟩
  by_contra! hth
  let r := (t-h).toNat
  have hr : 1 ≤ r := by dsimp [r]; omega
  have hri : (r:ℤ) = t-h := by dsimp [r]; omega
  have he : (∑' j : ℤ, b j * c (j-r)) = b t * c h := by
    rw [tsum_eq_single t]
    · congr 2
      omega
    · intro j hj
      by_cases hbj : b j = 0
      · simp [hbj]
      · have htj := ht j hbj
        rw [hcmin _ (by omega), mul_zero]
  have hzero := hz r hr
  rw [he] at hzero
  exact (mul_ne_zero hbt hch) hzero

lemma DiscreteConvex.add_const {G : ℕ → ℝ} (h : DiscreteConvex G) (c : ℝ) :
    DiscreteConvex (fun n => G n+c) := by
  intro i j hij
  simpa only [add_sub_add_right_eq_sub] using h hij

lemma eventually_quadratic_lower {G : ℕ → ℝ} {a δ : ℝ} (hδa : δ < a)
    (ht : Tendsto (fun n => G n / (n:ℝ)^2) atTop (𝓝 a)) :
    ∀ᶠ n : ℕ in atTop, δ*(n:ℝ)^2 ≤ G n := by
  filter_upwards [ht (eventually_gt_nhds hδa), eventually_ge_atTop 1] with n hn hn1
  have hnpos : 0 < (n:ℝ)^2 := sq_pos_of_pos (Nat.cast_pos.mpr (by omega))
  exact ((lt_div_iff₀ hnpos).mp hn).le




theorem quadratic_support_separation (w : ℤ → ℝ) (hw : QuadraticWeights w) :
    SupportSeparation w := by
  let W := fun j : ℤ => w j / w 0
  have hw0 : 0 < w 0 := hw.positive 0
  have hWpos (j : ℤ) : 0 < W j := div_pos (hw.positive j) hw0
  have hWdec : Antitone W := by
    intro i j hij
    exact div_le_div_of_nonneg_right (hw.decreasing hij) hw0.le
  have hW0 : W 0 = 1 := div_self (ne_of_gt hw0)
  have hlog (j : ℤ) : Real.log (w j / w 0) = Real.log (w j) - Real.log (w 0) :=
    Real.log_div (ne_of_gt (hw.positive j)) (ne_of_gt hw0)
  have hP : DiscreteConvex (negativeLog W) := by
    have heq : negativeLog W = fun n : ℕ => Real.log (w (-(n:ℤ))) + -Real.log (w 0) := by
      funext n
      simp only [negativeLog, W, hlog, sub_eq_add_neg]
    rw [heq]
    exact hw.convex_negative.add_const _
  have hQ : DiscreteConvex (positiveLog W) := by
    have heq : positiveLog W = fun n : ℕ => -Real.log (w n) + Real.log (w 0) := by
      funext n
      simp only [positiveLog, W, hlog]
      ring
    rw [heq]
    exact hw.concave_positive.add_const _
  obtain ⟨a, ha, hqa, hpa⟩ := hw.quadratic
  have hnat : Tendsto (fun n : ℕ => (n:ℝ)^2) atTop atTop := by
    exact (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp tendsto_natCast_atTop_atTop
  have hsmall : Tendsto (fun n : ℕ => Real.log (w 0) / (n:ℝ)^2) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp hnat).const_mul (Real.log (w 0))
  have htP : Tendsto (fun n : ℕ => negativeLog W n / (n:ℝ)^2) atTop (𝓝 a) := by
    simpa only [negativeLog, W, hlog, sub_div, sub_zero] using hpa.sub hsmall
  have htQ : Tendsto (fun n : ℕ => positiveLog W n / (n:ℝ)^2) atTop (𝓝 a) := by
    have heq : (fun n : ℕ => positiveLog W n / (n:ℝ)^2) =
        (fun n : ℕ => -(Real.log (w n) / (n:ℝ)^2) + Real.log (w 0) / (n:ℝ)^2) := by
      funext n
      simp only [positiveLog, W, hlog]
      ring
    rw [heq]
    simpa only [neg_neg, add_zero] using hqa.neg.add hsmall
  obtain ⟨lam, hlam, hlama⟩ := exists_between ha
  obtain ⟨δ, hδ, hδa⟩ := exists_between hlama
  have hsep := normalized_support_separation hWpos hWdec hW0 hP hQ hlam hδ
    (eventually_quadratic_lower hδa htP) (eventually_quadratic_lower hδa htQ)
  intro b c hbn hcn hb hc hz
  let C : ℂ := (w 0 : ℂ)
  have hC : C ≠ 0 := by dsimp [C]; exact_mod_cast (ne_of_gt hw0)
  have hCnorm : ‖C‖ = w 0 := by simpa [C] using Real.norm_of_nonneg hw0.le
  let b' := fun j => b j / C
  let c' := fun j => C * c j
  have hbn' : ∃ j, b' j ≠ 0 := by
    obtain ⟨j, hj⟩ := hbn
    exact ⟨j, div_ne_zero hj hC⟩
  have hcn' : ∃ j, c' j ≠ 0 := by
    obtain ⟨j, hj⟩ := hcn
    exact ⟨j, mul_ne_zero hC hj⟩
  have hb' (j : ℤ) : ‖b' j‖ ≤ W j := by
    dsimp [b', W]
    rw [norm_div, hCnorm]
    exact div_le_div_of_nonneg_right (hb j) hw0.le
  have hc' (j : ℤ) : ‖c' j‖ * W j ≤ 1 := by
    dsimp [c', W]
    rw [norm_mul, hCnorm]
    have he : w 0 * ‖c j‖ * (w j / w 0) = ‖c j‖ * w j := by field_simp
    rw [he]
    exact hc j
  have hz' (r : ℕ) (hr : 1 ≤ r) : (∑' j : ℤ, b' j * c' (j-r)) = 0 := by
    have he (j : ℤ) : b' j * c' (j-r) = b j * c (j-r) := by
      dsimp [b', c']
      field_simp
    simp only [he]
    exact hz r hr
  have hh := hsep b' c' hbn' hcn' hb' hc' hz'
  simpa [b', c', hC] using hh


lemma SupportSeparation.of_bounded {w : ℤ → ℝ} (hsep : SupportSeparation w)
    {b c : ℤ → ℂ} (hbn : ∃ j, b j ≠ 0) (hcn : ∃ j, c j ≠ 0)
    {B C : ℝ} (hB : 0 < B) (hC : 0 < C)
    (hb : ∀ j, ‖b j‖ ≤ B*w j) (hc : ∀ j, ‖c j‖*w j ≤ C)
    (hz : ∀ r : ℕ, 1 ≤ r → (∑' j : ℤ, b j * c (j-r)) = 0) :
    ∃ t h : ℤ, b t ≠ 0 ∧ c h ≠ 0 ∧
      (∀ j, t < j → b j = 0) ∧ (∀ j, j < h → c j = 0) ∧ t ≤ h := by
  have hBC : (B:ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hB)
  have hCC : (C:ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hC)
  let b' := fun j => b j / (B:ℂ)
  let c' := fun j => c j / (C:ℂ)
  have hbn' : ∃ j, b' j ≠ 0 := by
    obtain ⟨j, hj⟩ := hbn
    exact ⟨j, div_ne_zero hj hBC⟩
  have hcn' : ∃ j, c' j ≠ 0 := by
    obtain ⟨j, hj⟩ := hcn
    exact ⟨j, div_ne_zero hj hCC⟩
  have hb' (j : ℤ) : ‖b' j‖ ≤ w j := by
    dsimp [b']
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hB.le]
    exact (div_le_iff₀ hB).mpr (by simpa only [mul_comm] using hb j)
  have hc' (j : ℤ) : ‖c' j‖*w j ≤ 1 := by
    dsimp [c']
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hC.le, div_mul_eq_mul_div]
    exact (div_le_one hC).mpr (hc j)
  have hz' (r : ℕ) (hr : 1 ≤ r) : (∑' j : ℤ, b' j * c' (j-r)) = 0 := by
    have he (j : ℤ) : b' j * c' (j-r) = (b j*c (j-r)) / ((B:ℂ)*(C:ℂ)) := by
      dsimp [b', c']; ring
    simp only [he, tsum_div_const, hz r hr, zero_div]
  have hh := hsep b' c' hbn' hcn' hb' hc' hz'
  simpa [b', c', hBC, hCC] using hh


end
end BackwardIntertwiners

end OAI
