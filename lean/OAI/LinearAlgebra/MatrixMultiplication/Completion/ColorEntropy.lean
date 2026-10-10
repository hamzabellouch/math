import OAI.LinearAlgebra.MatrixMultiplication.Completion.ColorLaws

namespace OAI

/-! Readable tensor completion and its finite arithmetic realization. -/

noncomputable section

universe uCoord

namespace MatrixMultiplication.CompletionColorLaws

open MatrixMultiplication.Foundation RecursiveCompletion CompletionLabels
open scoped BigOperators
attribute [local instance 10000] Classical.propDecidable Classical.decEq
attribute [local instance 11000] instDecidableEqFin

theorem finiteEntropy_scale {A : Type*} [Fintype A] (p : FiniteLaw A) (r : ℝ) :
    finiteEntropy (fun a => r * p.mass a) =
      entropyTerm r + r * finiteEntropy p.mass := by
  simp only [finiteEntropy, entropyTerm_mul, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum, p.total, one_mul]

variable {X Y Z : Type uCoord} [Fintype X] [Fintype Y] [Fintype Z]

theorem colorMix_entropy (S : FlaggedTensor X Y Z) (center output : Color)
    (hne : center ≠ output)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1) :
    finiteEntropy (colorMix S center output pc po α hα hα').mass =
      entropyTerm α + entropyTerm (1 - α) +
        α * finiteEntropy pc.mass + (1 - α) * finiteEntropy po.mass := by
  have hterm (a : Leaf S) :
      entropyTerm ((colorMix S center output pc po α hα hα').mass a) =
        entropyTerm (α * (pc.map Subtype.val).mass a) +
          entropyTerm ((1 - α) * (po.map Subtype.val).mass a) := by
    by_cases hc : leafColor S a = center
    · have ho : leafColor S a ≠ output := fun ho => hne (hc.symm.trans ho)
      rw [colorMix_mass, colorSlice_map_mass_zero S output po a ho]
      simp
    · rw [colorMix_mass, colorSlice_map_mass_zero S center pc a hc]
      simp
  calc
    finiteEntropy (colorMix S center output pc po α hα hα').mass =
        finiteEntropy (fun a => α * (pc.map Subtype.val).mass a) +
          finiteEntropy (fun a => (1 - α) * (po.map Subtype.val).mass a) := by
      simp only [finiteEntropy, hterm, Finset.sum_add_distrib]
    _ = _ := by
      rw [finiteEntropy_scale, finiteEntropy_scale,
        pc.map_entropy_of_injective Subtype.val Subtype.val_injective,
        po.map_entropy_of_injective Subtype.val Subtype.val_injective]
      ring

theorem iidColorLaw_entropy (S : FlaggedTensor X Y Z) (center output : Color)
    (hne : center ≠ output)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (m : ℕ) (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1) :
    finiteEntropy (iidColorLaw S center output pc po m α hα hα').mass =
      (m : ℝ) * (entropyTerm α + entropyTerm (1 - α) +
        α * finiteEntropy pc.mass + (1 - α) * finiteEntropy po.mass) := by
  rw [iidColorLaw, CompletionProductLaws.independentProduct_entropy]
  simp only [colorMix_entropy S center output hne pc po α hα hα',
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end MatrixMultiplication.CompletionColorLaws

end

end OAI
