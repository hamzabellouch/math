import OAI.Analysis.MarkovType.DyadicWeakType
import OAI.Analysis.MarkovType.DyadicTreeMartingale
import OAI.Analysis.MarkovType.DyadicBellman

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def dyadicInterpolationConstant (a₀ p a₁ B₀ B₁ : ℝ) : ℝ :=
  p * ((2 * B₀) ^ a₀ / (p - a₀) + (2 * B₁) ^ a₁ / (a₁ - p))

theorem dyadicInterpolationConstant_pos {a₀ p a₁ B₀ B₁ : ℝ}
    (ha₀ : 0 < a₀) (ha₀p : a₀ < p) (hpa₁ : p < a₁)
    (hB₀ : 0 < B₀) (hB₁ : 0 < B₁) :
    0 < dyadicInterpolationConstant a₀ p a₁ B₀ B₁ := by
  unfold dyadicInterpolationConstant
  exact mul_pos (ha₀.trans ha₀p) (add_pos
    (div_pos (Real.rpow_pos_of_pos (mul_pos (by norm_num) hB₀) _) (sub_pos.mpr ha₀p))
    (div_pos (Real.rpow_pos_of_pos (mul_pos (by norm_num) hB₁) _) (sub_pos.mpr hpa₁)))

theorem dyadic_strong_of_weak_types {a₀ p a₁ B₀ B₁ : ℝ}
    (ha₀ : 0 < a₀) (ha₀p : a₀ < p) (hpa₁ : p < a₁)
    (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁)
    (h₀ : ∀ N : ℕ, FiniteWeakType dyadicInputWeight (dyadicLaw N).mass
      (dyadicSynthesis N (E := E)) a₀ B₀)
    (h₁ : ∀ N : ℕ, FiniteWeakType dyadicInputWeight (dyadicLaw N).mass
      (dyadicSynthesis N (E := E)) a₁ B₁)
    (N : ℕ) (φ : DyadicAtom N → E) :
    finiteMoment (dyadicLaw N).mass p (dyadicSynthesis N φ) ≤
      dyadicInterpolationConstant a₀ p a₁ B₀ B₁ * finiteMoment dyadicInputWeight p φ :=
  finite_marcinkiewicz dyadicInputWeight dyadicInputWeight_nonneg (dyadicLaw N).mass
    (dyadicLaw N).mass_nonneg (dyadicSynthesis N)
    ha₀ ha₀p hpa₁ hB₀ hB₁ (h₀ N) (h₁ N) φ

theorem finiteDyadicUpperEstimate_of_uniformStrong {p K : ℝ} (hp : 0 < p)
    (hstrong : ∀ (N : ℕ) (φ : DyadicAtom N → E),
      finiteMoment (dyadicLaw N).mass p (dyadicSynthesis N φ) ≤
        K * finiteMoment dyadicInputWeight p φ) :
    FiniteDyadicUpperEstimate (X := E) p K K := by
  intro t
  obtain ⟨N, φ, hroot, hmoment, henergy⟩ := DyadicTree.exists_dyadic_model t hp
  have h := hstrong N φ
  rw [hmoment, dyadicInputMoment, hroot, henergy, mul_add] at h
  exact h

theorem finiteDyadicUpperEstimate_of_uniformWeakTypes {a₀ p a₁ B₀ B₁ : ℝ}
    (ha₀ : 0 < a₀) (ha₀p : a₀ < p) (hpa₁ : p < a₁)
    (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁)
    (h₀ : ∀ N : ℕ, FiniteWeakType dyadicInputWeight (dyadicLaw N).mass
      (dyadicSynthesis N (E := E)) a₀ B₀)
    (h₁ : ∀ N : ℕ, FiniteWeakType dyadicInputWeight (dyadicLaw N).mass
      (dyadicSynthesis N (E := E)) a₁ B₁) :
    FiniteDyadicUpperEstimate (X := E) p
      (dyadicInterpolationConstant a₀ p a₁ B₀ B₁)
      (dyadicInterpolationConstant a₀ p a₁ B₀ B₁) :=
  finiteDyadicUpperEstimate_of_uniformStrong (ha₀.trans ha₀p)
    (dyadic_strong_of_weak_types ha₀ ha₀p hpa₁ hB₀ hB₁ h₀ h₁)

theorem dyadic_strong_of_weak_family {p r : ℝ}
    (hp : 1 < p) (hpr : p < r)
    (hweak : ∀ a : ℝ, 1 < a → a < r → ∃ B : ℝ, 0 < B ∧
      ∀ N : ℕ, FiniteWeakType dyadicInputWeight (dyadicLaw N).mass
        (dyadicSynthesis N (E := E)) a B) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ) (φ : DyadicAtom N → E),
      finiteMoment (dyadicLaw N).mass p (dyadicSynthesis N φ) ≤
        K * finiteMoment dyadicInputWeight p φ := by
  let a₀ := (1 + p) / 2
  let a₁ := (p + r) / 2
  have ha₀one : 1 < a₀ := by dsimp [a₀]; linarith
  have ha₀p : a₀ < p := by dsimp [a₀]; linarith
  have hpa₁ : p < a₁ := by dsimp [a₁]; linarith
  have ha₁r : a₁ < r := by dsimp [a₁]; linarith
  have ha₀ : 0 < a₀ := by linarith
  obtain ⟨B₀, hB₀, h₀⟩ := hweak a₀ ha₀one (ha₀p.trans hpr)
  obtain ⟨B₁, hB₁, h₁⟩ := hweak a₁ (hp.trans hpa₁) ha₁r
  exact ⟨dyadicInterpolationConstant a₀ p a₁ B₀ B₁,
    dyadicInterpolationConstant_pos ha₀ ha₀p hpa₁ hB₀ hB₁,
    dyadic_strong_of_weak_types ha₀ ha₀p hpa₁
      hB₀.le hB₁.le h₀ h₁⟩

theorem dyadic_strong_of_normalizedWeakMax {p r : ℝ}
    (hp : 1 < p) (hpr : p < r)
    (hmax : ∀ a : ℝ, 1 < a → a < r →
      ∃ A : ℝ, 1 ≤ A ∧ DyadicNormalizedWeakMax E a A) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ) (φ : DyadicAtom N → E),
      finiteMoment (dyadicLaw N).mass p (dyadicSynthesis N φ) ≤
        K * finiteMoment dyadicInputWeight p φ := by
  apply dyadic_strong_of_weak_family hp hpr
  intro a ha har
  obtain ⟨A, hA, hmaxA⟩ := hmax a ha har
  have ha0 : 0 < a := by linarith
  refine ⟨dyadicWeakNorm a A, dyadicWeakNorm_pos ha0 hA, ?_⟩
  exact fun N => dyadic_weak_type ha0 hA hmaxA N

theorem finiteDyadicUpperEstimate_of_normalizedWeakMax {p r : ℝ}
    (hp : 1 < p) (hpr : p < r)
    (hmax : ∀ a : ℝ, 1 < a → a < r →
      ∃ A : ℝ, 1 ≤ A ∧ DyadicNormalizedWeakMax E a A) :
    ∃ K : ℝ, 0 < K ∧ FiniteDyadicUpperEstimate (X := E) p K K := by
  obtain ⟨K, hK, hstrong⟩ := dyadic_strong_of_normalizedWeakMax hp hpr hmax
  exact ⟨K, hK, finiteDyadicUpperEstimate_of_uniformStrong (by linarith) hstrong⟩

end MarkovSuperreflexivity

end

end OAI
