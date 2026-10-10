import OAI.Geometry.HeilbronnTriangle.DigitColumnLaw
import OAI.Geometry.HeilbronnTriangle.BadTripleAverage
import OAI.Geometry.HeilbronnTriangle.FiniteFieldLabels

namespace OAI


noncomputable section

namespace Problem355.DigitBadTripleAverage

open scoped BigOperators
open DigitColumnLaw

def labelTripleEquiv (Λ : Type*) : (Fin 3 → Λ) ≃ Λ × Λ × Λ where
  toFun l := (l 0, l 1, l 2)
  invFun t := ![t.1, t.2.1, t.2.2]
  left_inv l := by funext i; fin_cases i <;> rfl
  right_inv t := rfl

theorem uniform_label_average {Λ : Type*} [Fintype Λ]
    (F : (Fin 3 → Λ) → ℝ) :
    (∑ l : Fin 3 → Λ, uniformWeight (Fin 3 → Λ) l * F l) =
      (∑ a : Λ, ∑ b : Λ, ∑ c : Λ, F ![a, b, c]) /
        (Fintype.card Λ : ℝ) ^ 3 := by
  classical
  calc
    _ = ∑ t : Λ × Λ × Λ,
        F ![t.1, t.2.1, t.2.2] / (Fintype.card Λ : ℝ) ^ 3 := by
      apply Fintype.sum_equiv (labelTripleEquiv Λ)
      intro l
      change uniformWeight (Fin 3 → Λ) l * F l =
        F ![l 0, l 1, l 2] / (Fintype.card Λ : ℝ) ^ 3
      have hl : (![l 0, l 1, l 2] : Fin 3 → Λ) = l := by
        funext i; fin_cases i <;> rfl
      simp [uniformWeight, hl, div_eq_mul_inv, mul_comm]
    _ = _ := by simp only [Fintype.sum_prod_type, Finset.sum_div]

lemma injective_labels {Λ : Type*} {a b c : Λ}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Function.Injective (![a, b, c] : Fin 3 → Λ) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

theorem expectation_le_six {Λ X : Type*}
    [Fintype Λ] [Nonempty Λ] [Fintype X] {k : ℕ}
    (D probability : (Fin 3 → Λ) → Array X k → ℝ)
    (A : ℝ) (hA : 0 ≤ A)
    (hmoment : ∀ labels,
      (∑ f : Array X k, uniformWeight (Array X k) f * D labels f) ≤ 2)
    (hzero : ∀ labels f, Function.Injective labels → probability labels f = 0)
    (hbad : ∀ labels f, ¬ Function.Injective labels →
      probability labels f ≤ A * D labels f) :
    (∑ s : Fin 3 → Latent Λ X k,
      ConditionalSamples.productWeight (uniformWeight (Latent Λ X k)) s *
        probability (tripleEquiv s).1 (tripleEquiv s).2) ≤
      6 * A / (Fintype.card Λ : ℝ) := by
  classical
  rw [expectation_triple, uniform_label_average]
  apply Sampling.bad_triple_average_le_six
    (fun _ _ _ f => uniformWeight (Array X k) f)
    (fun a b c f => D ![a, b, c] f)
    (fun a b c f => probability ![a, b, c] f) A hA
  · intro a b c f
    exact uniformWeight_nonneg _ f
  · intro a b c
    exact hmoment ![a, b, c]
  · intro a b c f hab hac hbc
    exact hzero _ f (injective_labels hab hac hbc)
  · intro a b c f hrep
    apply hbad
    intro hinj
    rcases hrep with hab | hac | hbc
    · have h := hinj (show (![a, b, c] : Fin 3 → Λ) 0 = ![a, b, c] 1 from hab)
      exact (by decide : (0 : Fin 3) ≠ 1) h
    · have h := hinj (show (![a, b, c] : Fin 3 → Λ) 0 = ![a, b, c] 2 from hac)
      exact (by decide : (0 : Fin 3) ≠ 2) h
    · have h := hinj (show (![a, b, c] : Fin 3 → Λ) 1 = ![a, b, c] 2 from hbc)
      exact (by decide : (1 : Fin 3) ≠ 2) h

theorem latent_expectation_le_six {Λ X : Type*}
    [Fintype Λ] [Nonempty Λ] [Fintype X] {k : ℕ}
    (D probability : (Fin 3 → Latent Λ X k) → ℝ)
    (A : ℝ) (hA : 0 ≤ A)
    (hmoment : ∀ labels,
      (∑ f : Array X k, uniformWeight (Array X k) f *
        D (tripleEquiv.symm (labels, f))) ≤ 2)
    (hzero : ∀ s, Function.Injective (fun i => (s i).1) → probability s = 0)
    (hbad : ∀ s, ¬ Function.Injective (fun i => (s i).1) →
      probability s ≤ A * D s) :
    (∑ s : Fin 3 → Latent Λ X k,
      ConditionalSamples.productWeight (uniformWeight (Latent Λ X k)) s *
        probability s) ≤ 6 * A / (Fintype.card Λ : ℝ) := by
  have h := expectation_le_six
    (fun labels f => D (tripleEquiv.symm (labels, f)))
    (fun labels f => probability (tripleEquiv.symm (labels, f))) A hA hmoment
    (fun labels f hi => hzero _ hi) (fun labels f hi => hbad _ hi)
  simpa only [Prod.mk.eta, Equiv.symm_apply_apply] using h

theorem expectation_le_six_prime_labels {r : ℕ} [Fact r.Prime]
    [Fintype (FiniteFieldLabels.Label r)] {X : Type*} [Fintype X] {k : ℕ}
    (D probability : (Fin 3 → FiniteFieldLabels.Label r) → Array X k → ℝ)
    (A : ℝ) (hA : 0 ≤ A)
    (hmoment : ∀ labels,
      (∑ f : Array X k, uniformWeight (Array X k) f * D labels f) ≤ 2)
    (hzero : ∀ labels f, Function.Injective labels → probability labels f = 0)
    (hbad : ∀ labels f, ¬ Function.Injective labels →
      probability labels f ≤ A * D labels f) :
    (∑ s : Fin 3 → Latent (FiniteFieldLabels.Label r) X k,
      ConditionalSamples.productWeight
        (uniformWeight (Latent (FiniteFieldLabels.Label r) X k)) s *
        probability (tripleEquiv s).1 (tripleEquiv s).2) ≤
      6 * A / (r : ℝ) ^ 41 := by
  have hc : Fintype.card (FiniteFieldLabels.Label r) = r ^ 41 := by
    rw [← Nat.card_eq_fintype_card, FiniteFieldLabels.card_label]
    rfl
  simpa only [hc, Nat.cast_pow] using
    expectation_le_six D probability A hA hmoment hzero hbad

theorem expectation_le_of_lifting_bound {r : ℕ} [Fact r.Prime]
    [Fintype (FiniteFieldLabels.Label r)] {X : Type*} [Fintype X] {k : ℕ}
    (D probability : (Fin 3 → FiniteFieldLabels.Label r) → Array X k → ℝ)
    (C R h N : ℝ) (hC : 0 ≤ C) (hh : 0 ≤ h) (hN : 0 < N)
    (hmoment : ∀ labels,
      (∑ f : Array X k, uniformWeight (Array X k) f * D labels f) ≤ 2)
    (hzero : ∀ labels f, Function.Injective labels → probability labels f = 0)
    (hbad : ∀ labels f, ¬ Function.Injective labels →
      probability labels f ≤ (64 / 21 : ℝ) * C * R ^ 2 * h * D labels f / N ^ 3) :
    (∑ s : Fin 3 → Latent (FiniteFieldLabels.Label r) X k,
      ConditionalSamples.productWeight
        (uniformWeight (Latent (FiniteFieldLabels.Label r) X k)) s *
        probability (tripleEquiv s).1 (tripleEquiv s).2) ≤
      (128 / 7 : ℝ) * C * R ^ 2 * h / (N ^ 3 * (r : ℝ) ^ 41) := by
  have hbound := expectation_le_six_prime_labels D probability
    ((64 / 21 : ℝ) * C * R ^ 2 * h / N ^ 3) (by positivity)
    hmoment hzero (by
      intro labels f hi
      convert hbad labels f hi using 1; ring)
  convert hbound using 1; ring

end Problem355.DigitBadTripleAverage

namespace Problem355.DigitColumnLaw

open scoped BigOperators

def labelsEquiv (Λ : Type*) : (Fin 3 → Λ) ≃ Λ × Λ × Λ where
  toFun l := (l 0, l 1, l 2)
  invFun t := ![t.1, t.2.1, t.2.2]
  left_inv l := by funext i; fin_cases i <;> rfl
  right_inv t := rfl

theorem expectation_labels_le_of_repeated
    {Λ : Type*} [Fintype Λ] [DecidableEq Λ] [Nonempty Λ]
    (F : (Fin 3 → Λ) → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ l, F l ≤ M)
    (hzero : ∀ l, l 0 ≠ l 1 → l 0 ≠ l 2 → l 1 ≠ l 2 → F l = 0) :
    (∑ l : Fin 3 → Λ, uniformWeight (Fin 3 → Λ) l * F l) ≤
      3 * M / (Fintype.card Λ : ℝ) := by
  have h := Sampling.average_repeated_labels_le
    (fun a b c => F ![a, b, c]) M hM
    (fun a b c => hbound _) (fun a b c hab hac hbc => hzero _ hab hac hbc)
  have hs : (∑ l : Fin 3 → Λ, F l) = ∑ a, ∑ b, ∑ c, F ![a, b, c] := by
    calc
      _ = ∑ t : Λ × Λ × Λ, F ((labelsEquiv Λ).symm t) :=
        (labelsEquiv Λ).symm.sum_comp F |>.symm
      _ = _ := by simp only [Fintype.sum_prod_type]; rfl
  have he : (∑ l : Fin 3 → Λ, uniformWeight (Fin 3 → Λ) l * F l) =
      (∑ l : Fin 3 → Λ, F l) / (Fintype.card Λ : ℝ) ^ 3 := by
    unfold uniformWeight
    rw [← Finset.mul_sum]
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    ring
  rw [he, hs]
  exact h

theorem expectation_triple_le_of_repeated
    {Λ X : Type*} [Fintype Λ] [DecidableEq Λ] [Nonempty Λ] [Fintype X] {k : ℕ}
    (F : (Fin 3 → Λ) → Array X k → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ l, (∑ f : Array X k, uniformWeight (Array X k) f * F l f) ≤ M)
    (hzero : ∀ l f, l 0 ≠ l 1 → l 0 ≠ l 2 → l 1 ≠ l 2 → F l f = 0) :
    (∑ s : Fin 3 → Latent Λ X k,
      ConditionalSamples.productWeight (uniformWeight (Latent Λ X k)) s *
        F (tripleEquiv s).1 (tripleEquiv s).2) ≤
      3 * M / (Fintype.card Λ : ℝ) := by
  rw [expectation_triple]
  apply expectation_labels_le_of_repeated _ M hM hbound
  intro l hab hac hbc
  simp only [hzero l _ hab hac hbc, mul_zero, Finset.sum_const_zero]

theorem bad_triple_expectation_le
    {Λ X : Type*} [Fintype Λ] [DecidableEq Λ] [Nonempty Λ] [Fintype X] {k : ℕ}
    (D : (Fin 3 → Λ) → Array X k → ℝ)
    (p : (Fin 3 → Latent Λ X k) → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hmoment : ∀ l, (∑ f : Array X k, uniformWeight (Array X k) f * D l f) ≤ 2)
    (hbound : ∀ l f, p (tripleEquiv.symm (l, f)) ≤ A * D l f)
    (hzero : ∀ s, (s 0).1 ≠ (s 1).1 → (s 0).1 ≠ (s 2).1 →
      (s 1).1 ≠ (s 2).1 → p s = 0) :
    (∑ s : Fin 3 → Latent Λ X k,
      ConditionalSamples.productWeight (uniformWeight (Latent Λ X k)) s * p s) ≤
      6 * A / (Fintype.card Λ : ℝ) := by
  have h := expectation_triple_le_of_repeated
    (fun l f => p (tripleEquiv.symm (l, f))) (A * 2) (by positivity)
    (by
      intro l
      calc
        _ ≤ ∑ f : Array X k, uniformWeight (Array X k) f * (A * D l f) :=
          Finset.sum_le_sum fun f _ => mul_le_mul_of_nonneg_left
            (hbound l f) (uniformWeight_nonneg _ f)
        _ = A * ∑ f : Array X k, uniformWeight (Array X k) f * D l f := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro f _
          ring
        _ ≤ A * 2 := mul_le_mul_of_nonneg_left (hmoment l) hA)
    (by intro l f hab hac hbc; exact hzero _ hab hac hbc)
  simpa only [Prod.mk.eta, Equiv.symm_apply_apply,
    show 3 * (A * 2) = 6 * A by ring] using h

end Problem355.DigitColumnLaw

end

end OAI
