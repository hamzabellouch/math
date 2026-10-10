import OAI.GroupTheory.PolycyclicRecognition.Algebra.ComplexificationRealForm

namespace OAI

/-! # Complexification preserves the chosen real Cartan algebra -/

noncomputable section
namespace PolycyclicRecognition

open LieAlgebra
open scoped TensorProduct

variable (L : Type*) [LieRing L] [LieAlgebra ℝ L]

theorem complexificationRealPart_lie_one (x : ℂ ⊗[ℝ] L) (h : L) :
    complexificationRealPart L ⁅x, (1 : ℂ) ⊗ₜ[ℝ] h⁆ =
      ⁅complexificationRealPart L x, h⁆ := by
  induction x using TensorProduct.inductionOn with
  | tmul z x => simp [smul_lie]
  | add x y hx hy => simp [add_lie, hx, hy]

theorem complexificationImagPart_lie_one (x : ℂ ⊗[ℝ] L) (h : L) :
    complexificationImagPart L ⁅x, (1 : ℂ) ⊗ₜ[ℝ] h⁆ =
      ⁅complexificationImagPart L x, h⁆ := by
  induction x using TensorProduct.inductionOn with
  | tmul z x => simp [smul_lie]
  | add x y hx hy => simp [add_lie, hx, hy]

instance complexifiedSubalgebra_isCartan (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra] :
    (complexifiedSubalgebra L H).IsCartanSubalgebra where
  nilpotent := (complexifiedInclusion L H).isNilpotent_range
  self_normalizing := by
    apply le_antisymm _ (complexifiedSubalgebra L H).le_normalizer
    intro x hx
    apply (mem_complexifiedSubalgebra_iff L H x).mpr
    have hn (h : L) (hh : h ∈ H) :
        complexificationRealPart L ⁅x, (1 : ℂ) ⊗ₜ[ℝ] h⁆ ∈ H ∧
        complexificationImagPart L ⁅x, (1 : ℂ) ⊗ₜ[ℝ] h⁆ ∈ H := by
      apply (mem_complexifiedSubalgebra_iff L H _).mp
      apply ((complexifiedSubalgebra L H).mem_normalizer_iff x).mp hx
      exact ⟨1 ⊗ₜ[ℝ] (⟨h, hh⟩ : H), rfl⟩
    constructor
    · have hr : complexificationRealPart L x ∈ H.normalizer := by
        apply (H.mem_normalizer_iff _).mpr
        intro h hh
        simpa only [complexificationRealPart_lie_one] using (hn h hh).1
      rwa [LieSubalgebra.IsCartanSubalgebra.self_normalizing] at hr
    · have hi : complexificationImagPart L x ∈ H.normalizer := by
        apply (H.mem_normalizer_iff _).mpr
        intro h hh
        simpa only [complexificationImagPart_lie_one] using (hn h hh).2
      rwa [LieSubalgebra.IsCartanSubalgebra.self_normalizing] at hi

end PolycyclicRecognition

end

end OAI
