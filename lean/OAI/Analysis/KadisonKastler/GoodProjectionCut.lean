import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith

namespace OAI

/-! # Selecting one projection cut from averaged estimates

A small mean displacement and a strictly larger mean commutator gap
give one cut satisfying both pointwise requirements. This is the scalar
selection step in Haagerup's projection-cut argument.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem exists_good_projection_cut_of_finite_measure [IsFiniteMeasure μ] (f g : X → ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hf₀ : ∀ x, 0 ≤ f x) (hg₁ : ∀ x, g x ≤ 1)
    (δ c : ℝ) (hδ : 0 < δ) (hc : 0 < c)
    (hmean : (∫ x, f x ∂μ) < δ * ((∫ x, g x ∂μ) - c * μ.real Set.univ)) :
    ∃ x, f x ≤ δ ∧ c ≤ g x := by
  let h : X → ℝ := fun x => g x - f x / δ - c
  have hint : 0 < ∫ x, h x ∂μ := by
    dsimp [h]
    have hs := integral_sub (hg.sub (hf.div_const δ))
      (integrable_const c : Integrable (fun _ : X => c) μ)
    have ht := integral_sub hg (hf.div_const δ)
    simp only [Pi.sub_apply] at hs ht
    rw [hs,ht,integral_div]
    simp only [integral_const,smul_eq_mul]
    have he : (∫ x, f x ∂μ) / δ < (∫ x, g x ∂μ) - c * μ.real Set.univ :=
      (div_lt_iff₀ hδ).mpr (by nlinarith [hmean])
    nlinarith
  have hex : ∃ x, 0 < h x := by
    by_contra hn
    push Not at hn
    exact (not_le_of_gt hint) (integral_nonpos hn)
  obtain ⟨x,hx⟩ := hex
  change 0 < g x - f x / δ - c at hx
  have hfdiv : 0 ≤ f x / δ := div_nonneg (hf₀ x) hδ.le
  have hfd : f x / δ < 1 := by linarith [hg₁ x]
  exact ⟨x,((div_lt_one hδ).mp hfd).le,by linarith⟩

theorem exists_good_projection_cut [IsProbabilityMeasure μ] (f g : X → ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hf₀ : ∀ x, 0 ≤ f x) (hg₁ : ∀ x, g x ≤ 1)
    (δ c : ℝ) (hδ : 0 < δ) (hc : 0 < c)
    (hmean : (∫ x, f x ∂μ) < δ * ((∫ x, g x ∂μ) - c)) :
    ∃ x, f x ≤ δ ∧ c ≤ g x := by
  let h : X → ℝ := fun x => g x - f x / δ - c
  have hint : 0 < ∫ x, h x ∂μ := by
    dsimp [h]
    have hs := integral_sub (hg.sub (hf.div_const δ))
      (integrable_const c : Integrable (fun _ : X => c) μ)
    have ht := integral_sub hg (hf.div_const δ)
    simp only [Pi.sub_apply] at hs ht
    rw [hs,ht,integral_div]
    simp only [integral_const,probReal_univ,one_smul]
    have he : (∫ x, f x ∂μ) / δ < (∫ x, g x ∂μ) - c :=
      (div_lt_iff₀ hδ).mpr (by nlinarith [hmean])
    linarith
  have hex : ∃ x, 0 < h x := by
    by_contra hn
    push Not at hn
    exact (not_le_of_gt hint) (integral_nonpos hn)
  obtain ⟨x,hx⟩ := hex
  change 0 < g x - f x / δ - c at hx
  have hfdiv : 0 ≤ f x / δ := div_nonneg (hf₀ x) hδ.le
  have hfd : f x / δ < 1 := by linarith [hg₁ x]
  exact ⟨x,((div_lt_one hδ).mp hfd).le,by linarith⟩

end

end KadisonKastler

end OAI
