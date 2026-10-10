import OAI.NumberTheory.TwoPoint.Bounds.RoughSieveProbability
import OAI.NumberTheory.TwoPoint.Bounds.RoughFourier

namespace OAI

/-! Passing from actual uniform samples to subset and additive-energy
counts. Every additive quadruple is injected into its first three entries. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

lemma uniformFiniteLaw_probability {α : Type*} [Fintype α] [Nonempty α]
    (E : α → Prop) : (uniformFiniteLaw α).probability E =
      ((univ.filter E).card : ℝ) / Fintype.card α := by
  simp only [FiniteLaw.probability, FiniteLaw.average, uniformFiniteLaw, ← mul_sum,
    sum_boole]
  ring

noncomputable def roughIntervalSamples (P : Finset ℕ) (A N : ℕ) : Finset (Fin N) :=
  univ.filter (fun j => avoidsPrimeSet P (A + j.val))

noncomputable def roughCubeSamples (P : Finset ℕ) (A : ℕ × ℕ × ℕ) (N : ℕ) :
    Finset (Fin N × Fin N × Fin N) :=
  univ.filter (fun j => fourFormsAvoidPrimeSet P
    (A.1 + j.1.val, A.2.1 + j.2.1.val, A.2.2 + j.2.2.val))

lemma roughIntervalSamples_probability (P : Finset ℕ) (A N : ℕ) [NeZero N] :
    (roughIntervalSamples P A N).card = (N : ℝ) *
      (uniformFiniteLaw (Fin N)).probability (fun j => avoidsPrimeSet P (A + j.val)) := by
  rw [uniformFiniteLaw_probability]
  simp only [Fintype.card_fin, roughIntervalSamples]
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  field_simp [hN]

lemma roughCubeSamples_probability (P : Finset ℕ) (A : ℕ × ℕ × ℕ) (N : ℕ)
    [NeZero N] :
    (roughCubeSamples P A N).card = (N : ℝ) ^ 3 *
      (uniformFiniteLaw (Fin N × Fin N × Fin N)).probability
        (fun j => fourFormsAvoidPrimeSet P
          (A.1 + j.1.val, A.2.1 + j.2.1.val, A.2.2 + j.2.2.val)) := by
  rw [uniformFiniteLaw_probability]
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, roughCubeSamples]
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  field_simp [hN]

theorem rough_subset_card_le (P Z : Finset ℕ) (A N : ℕ)
    (hZ : ∀ z ∈ Z, A ≤ z ∧ z < A + N ∧ avoidsPrimeSet P z) :
    Z.card ≤ (roughIntervalSamples P A N).card := by
  let offset (z : Z) : Fin N := ⟨(z : ℕ) - A, by
    have hz := hZ z z.property
    omega⟩
  let f : Z → roughIntervalSamples P A N := fun z => ⟨offset z, by
    have hz := hZ z z.property
    simp only [roughIntervalSamples, mem_filter, mem_univ, true_and]
    change avoidsPrimeSet P (A + ((z : ℕ) - A))
    rw [Nat.add_sub_of_le hz.1]
    exact hz.2.2⟩
  have hf : Function.Injective f := by
    intro z w he
    have hv := congrArg (fun t : roughIntervalSamples P A N => (t : Fin N).val) he
    have hz := hZ z z.property
    have hw := hZ w w.property
    apply Subtype.ext
    change (z : ℕ) - A = (w : ℕ) - A at hv
    omega
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf

noncomputable def additiveQuadruples (Z : Finset ℕ) :
    Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  ((Z ×ˢ Z) ×ˢ (Z ×ˢ Z)).filter (fun q => q.1.1 + q.1.2 = q.2.1 + q.2.2)

lemma mem_additiveQuadruples {Z : Finset ℕ} {q : (ℕ × ℕ) × (ℕ × ℕ)}
    (hq : q ∈ additiveQuadruples Z) :
    q.1.1 ∈ Z ∧ q.1.2 ∈ Z ∧ q.2.1 ∈ Z ∧ q.2.2 ∈ Z ∧
      q.1.1 + q.1.2 = q.2.1 + q.2.2 := by
  simpa only [additiveQuadruples, mem_filter, mem_product, and_assoc] using hq

theorem rough_additiveQuadruples_card_le (P Z : Finset ℕ) (A N : ℕ)
    (hZ : ∀ z ∈ Z, A ≤ z ∧ z < A + N ∧ avoidsPrimeSet P z) :
    (additiveQuadruples Z).card ≤ (roughCubeSamples P (A, A, A) N).card := by
  let Q := additiveQuadruples Z
  have hq (q : Q) := mem_additiveQuadruples q.property
  let off (z : ℕ) (hz : z ∈ Z) : Fin N := ⟨z - A, by have := hZ z hz; omega⟩
  let f : Q → roughCubeSamples P (A, A, A) N := fun q =>
    ⟨(off q.val.1.1 (hq q).1, off q.val.1.2 (hq q).2.1,
        off q.val.2.1 (hq q).2.2.1), by
      have h₁ := hZ q.val.1.1 (hq q).1
      have h₂ := hZ q.val.1.2 (hq q).2.1
      have h₃ := hZ q.val.2.1 (hq q).2.2.1
      have h₄ := hZ q.val.2.2 (hq q).2.2.2.1
      simp only [roughCubeSamples, mem_filter, mem_univ, true_and]
      change fourFormsAvoidPrimeSet P
        (A + (q.val.1.1 - A), A + (q.val.1.2 - A), A + (q.val.2.1 - A))
      rw [Nat.add_sub_of_le h₁.1, Nat.add_sub_of_le h₂.1, Nat.add_sub_of_le h₃.1]
      refine ⟨h₁.2.2, h₂.2.2, h₃.2.2, ?_⟩
      intro p hp hd
      have he : (q.val.1.1 : ℤ) + q.val.1.2 - q.val.2.1 = q.val.2.2 := by
        have := (hq q).2.2.2.2
        omega
      rw [he] at hd
      exact h₄.2.2 p hp (Int.natCast_dvd_natCast.mp hd)⟩
  have hf : Function.Injective f := by
    intro q r he
    have he₁ := congrArg (fun t : roughCubeSamples P (A, A, A) N =>
      ((t : Fin N × Fin N × Fin N).1).val) he
    have he₂ := congrArg (fun t : roughCubeSamples P (A, A, A) N =>
      ((t : Fin N × Fin N × Fin N).2.1).val) he
    have he₃ := congrArg (fun t : roughCubeSamples P (A, A, A) N =>
      ((t : Fin N × Fin N × Fin N).2.2).val) he
    change q.val.1.1 - A = r.val.1.1 - A at he₁
    change q.val.1.2 - A = r.val.1.2 - A at he₂
    change q.val.2.1 - A = r.val.2.1 - A at he₃
    have hq₁ := (hZ q.val.1.1 (hq q).1).1
    have hq₂ := (hZ q.val.1.2 (hq q).2.1).1
    have hq₃ := (hZ q.val.2.1 (hq q).2.2.1).1
    have hr₁ := (hZ r.val.1.1 (hq r).1).1
    have hr₂ := (hZ r.val.1.2 (hq r).2.1).1
    have hr₃ := (hZ r.val.2.1 (hq r).2.2.1).1
    have hqe := (hq q).2.2.2.2
    have hre := (hq r).2.2.2.2
    apply Subtype.ext
    apply Prod.ext
    · apply Prod.ext <;> omega
    · apply Prod.ext <;> omega
  simpa only [Q, Fintype.card_coe] using Fintype.card_le_of_injective f hf

/-- The actual rough interval and three-variable sieve probabilities imply
both manuscript Fourier bounds, uniformly over every subset of rough integers. -/
theorem roughFourier_bounds_of_sieve (P Z : Finset ℕ) (D h : ℕ) [NeZero D]
    (hh : 0 < h) (L U V : ℝ)
    (hZ : ∀ z ∈ Z, D ≤ z ∧ z < D + D ∧ avoidsPrimeSet P z)
    (h₁ : (uniformFiniteLaw (Fin D)).probability
      (fun j => avoidsPrimeSet P (D + j.val)) ≤ U * L ^ (-99 / 100 : ℝ))
    (h₄ : (uniformFiniteLaw (Fin D × Fin D × Fin D)).probability
      (fun j => fourFormsAvoidPrimeSet P
        (D + j.1.val, D + j.2.1.val, D + j.2.2.val)) ≤ V * L ^ (-99 / 25 : ℝ)) :
    (∀ θ, ‖roughFourierPolynomial Z h θ‖ ≤ U * L ^ (-99 / 100 : ℝ)) ∧
      (∫ θ, ‖roughFourierPolynomial Z h θ‖ ^ 4 ∂AddCircle.haarAddCircle) ≤
        V / (D : ℝ) * L ^ (-99 / 25 : ℝ) := by
  have hD : (0 : ℝ) < D := by exact_mod_cast NeZero.pos D
  have hzr (z : ℕ) (hz : z ∈ Z) : (D : ℝ) ≤ z := by exact_mod_cast (hZ z hz).1
  have hc : (Z.card : ℝ) ≤ (D : ℝ) * (U * L ^ (-99 / 100 : ℝ)) := by
    calc
      _ ≤ ((roughIntervalSamples P D D).card : ℝ) := by
        exact_mod_cast rough_subset_card_le P Z D D hZ
      _ = _ := roughIntervalSamples_probability P D D
      _ ≤ _ := mul_le_mul_of_nonneg_left h₁ hD.le
  have hq : ((additiveQuadruples Z).card : ℝ) ≤
      (D : ℝ) ^ 3 * (V * L ^ (-99 / 25 : ℝ)) := by
    calc
      _ ≤ ((roughCubeSamples P (D, D, D) D).card : ℝ) := by
        exact_mod_cast rough_additiveQuadruples_card_le P Z D D hZ
      _ = _ := roughCubeSamples_probability P (D, D, D) D
      _ ≤ _ := mul_le_mul_of_nonneg_left h₄ (by positivity)
  constructor
  · intro θ
    apply (norm_roughFourierPolynomial_le Z h (D : ℝ) hD hzr θ).trans
    exact (div_le_iff₀ hD).mpr (by nlinarith only [hc])
  · calc
      _ ≤ ((additiveQuadruples Z).card : ℝ) * ((D : ℝ)⁻¹) ^ 4 :=
        roughFourierPolynomial_fourth_moment_le Z h hh (D : ℝ) hD hzr
      _ ≤ ((D : ℝ) ^ 3 * (V * L ^ (-99 / 25 : ℝ))) * ((D : ℝ)⁻¹) ^ 4 :=
        mul_le_mul_of_nonneg_right hq (by positivity)
      _ = _ := by field_simp

end TwoPointCorrelations

end OAI
