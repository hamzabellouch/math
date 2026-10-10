import OAI.NumberTheory.TwoPoint.Bounds.TraceDesignations

namespace OAI

/-! Group literal unlit factors and forced lit atoms into exact prime exponents. -/

namespace TwoPointCorrelations

open Finset

variable {ι τ : Type*} [Fintype ι] [DecidableEq ι]

lemma product_grouped_by_label (S : Finset τ) (label : τ → ι) (θ : ι → ℝ) :
    (∏ t ∈ S, θ (label t)) = ∏ i, θ i ^ (S.filter (fun t => label t = i)).card := by
  rw [← prod_fiberwise' S label θ]
  simp only [prod_const]

omit [Fintype ι] in
lemma mem_label_image_iff_count_pos (S : Finset τ) (label : τ → ι) (i : ι) :
    i ∈ S.image label ↔ 0 < (S.filter (fun t => label t = i)).card := by
  rw [card_pos, filter_nonempty_iff]
  exact mem_image

lemma label_image_product (S : Finset τ) (label : τ → ι) (θ : ι → ℝ) :
    (∏ i ∈ S.image label, θ i) =
      ∏ i, θ i ^ (if (S.filter (fun t => label t = i)).card = 0 then 0 else 1) := by
  have he : (∏ i ∈ S.image label, θ i) =
      ∏ i, if i ∈ S.image label then θ i else 1 := by
    rw [← prod_filter]
    congr 1
    ext i
    simp only [mem_filter, mem_univ, true_and]
  rw [he]
  apply prod_congr rfl
  intro i _
  have hi := mem_label_image_iff_count_pos S label i
  by_cases hc : (S.filter (fun t => label t = i)).card = 0
  · have hn : i ∉ S.image label := by simpa [hc] using hi
    simp [hc, hn]
  · have hm : i ∈ S.image label := hi.mpr (Nat.pos_of_ne_zero hc)
    simp [hc, hm]

/-- The modulus atom appears once if there is any lit occurrence; unlit
occurrences retain their individual scalar reciprocals. -/
lemma designated_weight_exponents (L U : Finset τ) (label : τ → ι) (θ : ι → ℝ) :
    (∏ t ∈ U, θ (label t)) * (∏ i ∈ L.image label, θ i) =
      ∏ i, θ i ^ litReciprocalExponent
        (L.filter (fun t => label t = i)).card (U.filter (fun t => label t = i)).card := by
  rw [product_grouped_by_label, label_image_product, ← prod_mul_distrib]
  apply prod_congr rfl
  intro i _
  rw [← pow_add]
  rfl

omit [Fintype ι] [DecidableEq ι] in
lemma absolute_unlit_coefficient (U : Finset τ) (label : τ → ι) (θ : ι → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) :
    |(-1 : ℝ) ^ U.card * ∏ t ∈ U, θ (label t)| = ∏ t ∈ U, θ (label t) := by
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  exact abs_of_nonneg (prod_nonneg (fun t _ => hθ (label t)))

/-- Exact baseline extraction for the designated reciprocal coefficient. -/
theorem designated_reciprocal_extra_bound (L U : Finset τ) (label : τ → ι)
    (p : ι → ℝ) (H : ℝ)
    (hcount : ∀ i, 2 ≤ (L.filter (fun t => label t = i)).card +
      (U.filter (fun t => label t = i)).card)
    (hH : 0 < H) (hp : ∀ i, H ≤ p i) :
    (∏ t ∈ U, (p (label t))⁻¹) * (∏ i ∈ L.image label, (p i)⁻¹) ≤
      (∏ i, (p i)⁻¹) * H⁻¹ ^
        (∑ i, extraReciprocalExponent (L.filter (fun t => label t = i)).card
          (U.filter (fun t => label t = i)).card) := by
  rw [designated_weight_exponents L U label (fun i => (p i)⁻¹)]
  exact lit_reciprocal_product_bound _ _ p H hcount hH hp

/-- Including singleton atoms gives exactly one basic reciprocal for every
observed label. Extra powers are still measured only by the nonsingleton
lit and unlit counts; singleton labels have both counts zero. -/
theorem designated_all_reciprocal_bound (S : Finset ι) (L U : Finset τ)
    (label : τ → ι) (p : ι → ℝ) (H : ℝ)
    (hzero : ∀ i ∈ S, (L.filter (fun t => label t = i)).card = 0 ∧
      (U.filter (fun t => label t = i)).card = 0)
    (hcount : ∀ i ∉ S, 2 ≤ (L.filter (fun t => label t = i)).card +
      (U.filter (fun t => label t = i)).card)
    (hH : 0 < H) (hp : ∀ i, H ≤ p i) :
    (∏ t ∈ U, (p (label t))⁻¹) * (∏ i ∈ L.image label, (p i)⁻¹) *
        (∏ i ∈ S, (p i)⁻¹) ≤
      (∏ i, (p i)⁻¹) * H⁻¹ ^
        (∑ i, extraReciprocalExponent (L.filter (fun t => label t = i)).card
          (U.filter (fun t => label t = i)).card) := by
  let E : ι → ℕ := fun i => extraReciprocalExponent
    (L.filter (fun t => label t = i)).card (U.filter (fun t => label t = i)).card
  have hs : (∏ i ∈ S, (p i)⁻¹) =
      ∏ i, (p i)⁻¹ ^ (if i ∈ S then 1 else 0) := by
    calc
      _ = ∏ i, if i ∈ S then (p i)⁻¹ else 1 := by
        rw [← prod_filter]
        simp
      _ = _ := by
        apply prod_congr rfl
        intro i _
        split_ifs <;> simp
  have he (i : ι) : litReciprocalExponent
      (L.filter (fun t => label t = i)).card (U.filter (fun t => label t = i)).card +
        (if i ∈ S then 1 else 0) = E i + 1 := by
    by_cases hi : i ∈ S
    · rcases hzero i hi with ⟨hl, hu⟩
      simp only [E, hl, hu, ite_eq_left hi, extraReciprocalExponent, litReciprocalExponent]
      norm_num
    · have hpos := litReciprocalExponent_pos _ _ (hcount i hi)
      simp only [hi, ite_false, add_zero]
      dsimp [E, extraReciprocalExponent]
      omega
  have hf : (∏ t ∈ U, (p (label t))⁻¹) * (∏ i ∈ L.image label, (p i)⁻¹) *
      (∏ i ∈ S, (p i)⁻¹) = (∏ i, (p i)⁻¹) * ∏ i, (p i)⁻¹ ^ E i := by
    rw [designated_weight_exponents L U label (fun i => (p i)⁻¹), hs,
      ← prod_mul_distrib, ← prod_mul_distrib]
    apply prod_congr rfl
    intro i _
    rw [← pow_add, he, pow_succ]
    ring
  rw [hf, ← prod_pow_eq_pow_sum]
  apply mul_le_mul_of_nonneg_left
  · apply prod_le_prod₀
    · intro i _
      exact pow_nonneg (inv_nonneg.mpr (hH.trans_le (hp i)).le) _
    · intro i _
      exact pow_le_pow_left₀ (inv_nonneg.mpr (hH.trans_le (hp i)).le)
        (inv_anti₀ hH (hp i)) _
  · exact prod_nonneg (fun i _ => inv_nonneg.mpr (hH.trans_le (hp i)).le)

end TwoPointCorrelations

end OAI
