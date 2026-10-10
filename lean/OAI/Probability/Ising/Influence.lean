import OAI.Probability.Ising.FieldUpdate

namespace OAI

open scoped BigOperators Classical

namespace BufferedIsing.DSS

noncomputable section

universe u

variable {V : Type u} [Fintype V]

lemma tanh_nonneg_of_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ Real.tanh t := by
  rw [Real.tanh_eq]
  exact div_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith)))
    (add_pos (Real.exp_pos _) (Real.exp_pos _)).le

lemma reference_update {z c : ℝ} (hc : 1 + z * c ≠ 0) :
    update z c = ((1 - c) / (1 + z * c)) * z + (1 - (1 - c) / (1 + z * c)) := by
  dsimp [update]
  field_simp
  ring

lemma update_neg (a c : ℝ) : update (-a) (-c) = -update a c := by
  simp only [update, neg_mul_neg]
  ring

lemma mixture_weight_range {z c : ℝ} (hz : 0 ≤ z) (hc0 : 0 ≤ c) (hc1 : c < 1) :
    0 ≤ (1 - c) / (1 + z * c) ∧ (1 - c) / (1 + z * c) ≤ 1 := by
  have hden : 0 < 1 + z * c := by nlinarith [mul_nonneg hz hc0]
  constructor
  · exact div_nonneg (by linarith) hden.le
  · apply (div_le_one hden).mpr
    nlinarith [mul_nonneg hz hc0]

/-- The induction step combines bounds for a smaller increment support and for pinned gaps. -/
lemma influence_step (J : V → V → ℝ) (hJ : ∀ u v, 0 ≤ J u v)
    (g h : V → ℝ) (hh : 0 ≤ h) (v o : V) (t : ℝ) (ht : 0 ≤ t)
    (Hfield : ∀ (g' : V → ℝ) (o' : V),
      mean J (g' + h) o' - mean J (g' - h) o' ≤ mean J h o' - mean J (-h) o')
    (Hpin : pinMean J (g + h) v true o - pinMean J (g - h) v false o ≤
      pinMean J h v true o - pinMean J (-h) v false o) :
    mean J ((g + h) + fieldAt v t) o - mean J ((g - h) + fieldAt v (-t)) o ≤
      mean J (h + fieldAt v t) o - mean J ((-h) + fieldAt v (-t)) o := by
  let a := mean J (g + h) v
  let b := mean J (g - h) v
  let z := mean J h v
  let c := Real.tanh t
  let α := (1 - c) / (1 + z * c)
  have ha : -1 < a ∧ a < 1 := ⟨neg_one_lt_mean _ _ _, mean_lt_one _ _ _⟩
  have hb : -1 < b ∧ b < 1 := ⟨neg_one_lt_mean _ _ _, mean_lt_one _ _ _⟩
  have hz0 : 0 ≤ z := mean_nonneg J hJ h hh v
  have hz1 : z < 1 := mean_lt_one J h v
  have hc : 0 ≤ c ∧ c < 1 := ⟨tanh_nonneg_of_nonneg ht, Real.tanh_lt_one t⟩
  have hab : b ≤ a := by
    apply mean_mono J hJ
    intro u
    dsimp
    exact le_trans (sub_le_self _ (hh u)) (le_add_of_nonneg_right (hh u))
  have hgap : a - b ≤ 2 * z := by
    have H := Hfield g v
    rw [mean_neg] at H
    dsimp [a, b, z]
    linarith
  obtain ⟨d, hd0, hd1, Hup, Hlo⟩ := interpolation ha hb hab hc hz0 hgap
  let s := Real.artanh d
  have hs : Real.tanh s = d := Real.tanh_artanh ⟨hd0, hd1⟩
  have hα : 0 ≤ α ∧ α ≤ 1 := mixture_weight_range hz0 hc.1 hc.2
  have Up : mean J ((g + h) + fieldAt v t) o ≤
      α * mean J ((g + h) + fieldAt v s) o + (1 - α) * pinMean J (g + h) v true o := by
    apply mean_mixture_le J hJ
    rw [mean_field_update, mean_field_update, hs]
    simpa only [sgn, ↓reduceIte, mul_one, update, a, α, c] using Hup
  have Lo : α * mean J ((g - h) + fieldAt v s) o + (1 - α) * pinMean J (g - h) v false o ≤
      mean J ((g - h) + fieldAt v (-t)) o := by
    apply mean_mixture_ge J hJ
    rw [mean_field_update, mean_field_update, Real.tanh_neg, hs]
    simpa only [sgn, Bool.false_eq_true, ↓reduceIte, mul_neg_one, sub_eq_add_neg,
      update, b, α, c] using Hlo
  have hzden : 1 + z * c ≠ 0 := (by nlinarith [mul_nonneg hz0 hc.1] : 0 < 1 + z * c).ne'
  have RefUp : mean J (h + fieldAt v t) o =
      α * mean J h o + (1 - α) * pinMean J h v true o := by
    have H := mean_mixture_eq J h v o t 0 α true
    simp only [fieldAt_zero, add_zero] at H
    apply H
    rw [mean_field_update]
    simpa only [sgn, ↓reduceIte, mul_one, update, z, α, c] using reference_update hzden
  have RefLo : mean J ((-h) + fieldAt v (-t)) o =
      α * mean J (-h) o + (1 - α) * pinMean J (-h) v false o := by
    have H := mean_mixture_eq J (-h) v o (-t) 0 α false
    simp only [fieldAt_zero, add_zero] at H
    apply H
    rw [mean_field_update, mean_neg, Real.tanh_neg]
    have He : update (-z) (-c) = α * (-z) - (1 - α) := by
      rw [update_neg, reference_update hzden]
      dsimp [α]
      ring
    simpa only [sgn, Bool.false_eq_true, ↓reduceIte, mul_neg_one, sub_eq_add_neg,
      update, z, α, c] using He
  have Hcommon : mean J ((g + h) + fieldAt v s) o - mean J ((g - h) + fieldAt v s) o ≤
      mean J h o - mean J (-h) o := by
    convert Hfield (g + fieldAt v s) o using 1
    congr 2 <;> ext u <;> simp <;> ring
  calc
    _ ≤ α * (mean J ((g + h) + fieldAt v s) o - mean J ((g - h) + fieldAt v s) o) +
        (1 - α) * (pinMean J (g + h) v true o - pinMean J (g - h) v false o) := by linarith
    _ ≤ α * (mean J h o - mean J (-h) o) +
        (1 - α) * (pinMean J h v true o - pinMean J (-h) v false o) :=
      add_le_add (mul_le_mul_of_nonneg_left Hcommon hα.1)
        (mul_le_mul_of_nonneg_left Hpin (sub_nonneg.mpr hα.2))
    _ = _ := by rw [RefUp, RefLo]; ring

/-- The nonnegative-increment influence bound for a fixed finite coupling array. -/
def InfluenceBound (J : V → V → ℝ) : Prop :=
  ∀ (g h : V → ℝ), 0 ≤ h → ∀ o : V,
    mean J (g + h) o - mean J (g - h) o ≤ mean J h o - mean J (-h) o

lemma pin_comparison_of_removed (J : V → V → ℝ) (hJ : ∀ u v, 0 ≤ J u v)
    (g h : V → ℝ) (hh : 0 ≤ h) (v o : V)
    (H : InfluenceBound (removedCoupling J v)) :
    pinMean J (g + h) v true o - pinMean J (g - h) v false o ≤
      pinMean J h v true o - pinMean J (-h) v false o := by
  by_cases hov : o = v
  · subst o
    simp only [pinMean_self, le_refl]
  · let g' : {u : V // u ≠ v} → ℝ := fun u => g u
    let h' : {u : V // u ≠ v} → ℝ := fun u => h u + (J v u + J u v)
    have hh' : 0 ≤ h' := by
      intro u
      exact add_nonneg (hh u) (add_nonneg (hJ v u) (hJ u v))
    have he1 : removedField J (g + h) v true = g' + h' := by
      ext u
      simp only [removedField, Pi.add_apply, sgn, ↓reduceIte, mul_one, g', h']
      ring
    have he2 : removedField J (g - h) v false = g' - h' := by
      ext u
      simp only [removedField, Pi.sub_apply, sgn, Bool.false_eq_true, ↓reduceIte,
        mul_neg_one, g', h']
      ring
    have he3 : removedField J h v true = h' := by
      ext u
      simp only [removedField, sgn, ↓reduceIte, mul_one, h']
    have he4 : removedField J (-h) v false = -h' := by
      ext u
      simp only [removedField, Pi.neg_apply, sgn, Bool.false_eq_true, ↓reduceIte,
        mul_neg_one, h']
      ring
    simp only [pinMean_other _ _ _ _ _ hov, he1, he2, he3, he4]
    exact H g' h' hh' ⟨o, hov⟩

def positiveSupport (h : V → ℝ) : Finset V := Finset.univ.filter (fun u => 0 < h u)

/-- The influence inequality follows by induction on the vertex count and the positive-increment support size. -/
theorem influence_of_card (n : ℕ) :
    ∀ (V : Type u) [Fintype V], Fintype.card V = n →
      ∀ (J : V → V → ℝ), (∀ u v, 0 ≤ J u v) → InfluenceBound J := by
  induction n using Nat.strong_induction_on with
  | h n ihn =>
    intro V inst hcard J hJ
    have Hm : ∀ k (g h : V → ℝ), 0 ≤ h → (positiveSupport h).card = k → ∀ o : V,
        mean J (g + h) o - mean J (g - h) o ≤ mean J h o - mean J (-h) o := by
      intro k
      induction k using Nat.strong_induction_on with
      | h k ihk =>
        intro g h hh hk o
        by_cases hex : ∃ v, 0 < h v
        · obtain ⟨v, hv⟩ := hex
          let h0 : V → ℝ := fun u => if u = v then 0 else h u
          have hh0 : 0 ≤ h0 := by
            intro u
            dsimp [h0]
            split_ifs
            · exact le_rfl
            · exact hh u
          have hsupport : positiveSupport h0 = (positiveSupport h).erase v := by
            ext u
            by_cases hu : u = v
            · subst u
              simp [positiveSupport, h0]
            · simp [positiveSupport, h0, hu]
          have hsmall : (positiveSupport h0).card < k := by
            rw [hsupport, ← hk]
            apply Finset.card_erase_lt_of_mem
            simp [positiveSupport, hv]
          have Hfield : ∀ (g' : V → ℝ) (o' : V),
              mean J (g' + h0) o' - mean J (g' - h0) o' ≤ mean J h0 o' - mean J (-h0) o' := by
            intro g' o'
            exact ihk _ hsmall g' h0 hh0 rfl o'
          have hnsmall : Fintype.card {u : V // u ≠ v} < n := by
            rw [← hcard]
            exact Fintype.card_subtype_lt (x := v) (by simp)
          have Hremoved : InfluenceBound (removedCoupling J v) :=
            ihn _ hnsmall {u : V // u ≠ v} rfl (removedCoupling J v) (fun u w => hJ u w)
          have Hpin := pin_comparison_of_removed J hJ g h0 hh0 v o Hremoved
          have Hstep := influence_step J hJ g h0 hh0 v o (h v) hv.le Hfield Hpin
          have he : h0 + fieldAt v (h v) = h := by
            ext u
            by_cases hu : u = v <;> simp [h0, fieldAt, hu]
          have hen : -h0 + fieldAt v (-h v) = -h := by
            ext u
            by_cases hu : u = v <;> simp [h0, fieldAt, hu]
          have hep : (g + h0) + fieldAt v (h v) = g + h := by rw [add_assoc, he]
          have hem : (g - h0) + fieldAt v (-h v) = g - h := by
            calc
              _ = g + (-h0 + fieldAt v (-h v)) := by abel
              _ = _ := by rw [hen]; rfl
          rw [hep, hem, he, hen] at Hstep
          exact Hstep
        · have hz : h = 0 := by
            ext u
            exact le_antisymm (le_of_not_gt (fun hu => hex ⟨u, hu⟩)) (hh u)
          subst h
          simp
    intro g h hh o
    exact Hm _ g h hh rfl o

/-- Arbitrary real background fields do not increase the influence of a finite
nonnegative perturbation, on every finite ferromagnetic graph. -/
theorem influence (J : V → V → ℝ) (hJ : ∀ u v, 0 ≤ J u v) : InfluenceBound J :=
  influence_of_card (Fintype.card V) V rfl J hJ

lemma pin_gap_comparison (J : V → V → ℝ) (hJ : ∀ u v, 0 ≤ J u v)
    (g : V → ℝ) (v o : V) :
    pinMean J g v true o - pinMean J g v false o ≤
      pinMean J 0 v true o - pinMean J 0 v false o := by
  have H := pin_comparison_of_removed J hJ g 0 (le_refl _) v o
    (influence (removedCoupling J v) (fun u w => hJ u w))
  simpa only [add_zero, sub_zero, neg_zero] using H

def correlation (J : V → V → ℝ) (h : V → ℝ) (u v : V) : ℝ :=
  average J h (fun σ => sgn (σ u) * sgn (σ v))

lemma sum_pin_first (J : V → V → ℝ) (h : V → ℝ) (v o : V) (b : Bool) :
    (∑ η, mass J h (insertSpin v b η) * sgn (insertSpin v b η o)) =
      pinPart J h v b * pinMean J h v b o := by
  simp_rw [mass_insert, mul_assoc, ← Finset.mul_sum]
  rw [pinPart, pinMean, mul_assoc, mul_comm (part _ _), average_mul_part]
  congr!

lemma correlation_split (J : V → V → ℝ) (h : V → ℝ) (u v : V) :
    correlation J h u v =
      (pinPart J h v true * pinMean J h v true u -
        pinPart J h v false * pinMean J h v false u) / part J h := by
  unfold correlation average
  rw [sum_insert v]
  simp only [insertSpin_self, show sgn true = 1 from rfl, show sgn false = -1 from rfl,
    mul_one, mul_neg, Finset.sum_neg_distrib, sum_pin_first, sub_eq_add_neg]

lemma covariance_identity (J : V → V → ℝ) (h : V → ℝ) (u v : V) :
    correlation J h u v - mean J h u * mean J h v =
      (1 - (mean J h v) ^ 2) * (pinMean J h v true u - pinMean J h v false u) / 2 := by
  rw [correlation_split, mean_split J h v u, mean_self_split J h v, part_split J h v]
  have hz : pinPart J h v true + pinPart J h v false ≠ 0 :=
    (add_pos (pinPart_pos _ _ _ _) (pinPart_pos _ _ _ _)).ne'
  field_simp
  ring

/-- Conditioning at a site and applying the influence inequality bounds arbitrary-field covariance by zero-field correlation. -/
theorem covariance_le_zero_field (J : V → V → ℝ) (hJ : ∀ u v, 0 ≤ J u v)
    (g : V → ℝ) (u v : V) :
    correlation J g u v - mean J g u * mean J g v ≤ correlation J 0 u v := by
  have hgap := pin_gap_comparison J hJ g v u
  have hnonneg := sub_nonneg.mpr (pinMean_mono J hJ g v u)
  have hprod := mul_nonneg (sq_nonneg (mean J g v)) hnonneg
  have hzero := covariance_identity J 0 u v
  simp only [mean_zero, zero_mul, sub_zero, zero_pow (by decide : 2 ≠ 0),
    sub_zero, one_mul] at hzero
  rw [covariance_identity]
  calc
    _ ≤ (pinMean J g v true u - pinMean J g v false u) / 2 := by nlinarith
    _ ≤ (pinMean J 0 v true u - pinMean J 0 v false u) / 2 := by linarith
    _ = correlation J 0 u v := hzero.symm

end

end BufferedIsing.DSS

end OAI
