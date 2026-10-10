import OAI.MeasureTheory.Falconer.Estimates.ClassRecombination

namespace OAI

/-! # The original class-pair weights have total mass at most one -/

namespace Falconer.Regularization
open Set MeasureTheory
open scoped ENNReal NNReal
variable {d : ℕ}

theorem retained_class_real_mass_sum_le_one (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ]
    {N : ℕ} {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N)
    (f : CellPath d → List ℕ) (F : Finset (List ℕ)) (hF : F ⊆ L.image f) :
    (∑ T ∈ F, (classMeasure Q μ L f T univ).toReal) ≤ 1 := by
  have hfinite (T : List ℕ) : classMeasure Q μ L f T univ ≠ ∞ := by
    change μ.restrict _ univ ≠ ∞
    exact measure_ne_top _ _
  rw [← ENNReal.toReal_sum (fun T _ => hfinite T)]
  exact (ENNReal.toReal_mono (by simp) (retained_class_mass_sum_le_one Q hQ μ hL f F hF)).trans_eq (by simp)

theorem retained_class_pair_real_mass_sum_le_one
    (Q₁ Q₂ : DyadicCube d) (hQ₁ : 0 < Q₁.side) (hQ₂ : 0 < Q₂.side)
    (μ ν : Measure (Space d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {N : ℕ} {L₁ L₂ : Finset (CellPath d)}
    (hL₁ : L₁ ⊆ cubePaths d N) (hL₂ : L₂ ⊆ cubePaths d N)
    (f₁ f₂ : CellPath d → List ℕ) (F G : Finset (List ℕ))
    (hF : F ⊆ L₁.image f₁) (hG : G ⊆ L₂.image f₂) :
    (∑ i ∈ F.product G,
      (classMeasure Q₁ μ L₁ f₁ i.1 univ * classMeasure Q₂ ν L₂ f₂ i.2 univ).toReal) ≤ 1 := by
  classical
  have he := Finset.sum_product F G (fun i : List ℕ × List ℕ =>
    (classMeasure Q₁ μ L₁ f₁ i.1 univ * classMeasure Q₂ ν L₂ f₂ i.2 univ).toReal)
  rw [Finset.product_eq_sprod,he]
  simp only [ENNReal.toReal_mul]
  rw [← Finset.sum_mul_sum]
  have h₁ := retained_class_real_mass_sum_le_one Q₁ hQ₁ μ hL₁ f₁ F hF
  have h₂ := retained_class_real_mass_sum_le_one Q₂ hQ₂ ν hL₂ f₂ G hG
  exact (mul_le_mul h₁ h₂ (Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg)) zero_le_one).trans_eq (one_mul 1)

end Falconer.Regularization

end OAI
