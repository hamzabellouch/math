import OAI.Algebra.Finitistic.Iteration.BinomialIteration

namespace OAI
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace ExternalTensor.Binomial
universe v u w
variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- A finite biproduct is zero exactly when all its summands are zero. -/
theorem isZero_biproduct_iff [HasFiniteBiproducts C] {I : Type} [Fintype I] (f : I → C) :
    IsZero (⨁ f) ↔ ∀ i, IsZero (f i) := by
  constructor
  · intro h i
    exact IsZero.of_mono (biproduct.ι f i) h
  · intro h
    apply (IsZero.iff_id_eq_zero _).mpr
    apply biproduct.hom_ext
    intro i
    exact (h i).eq_of_tgt _ _

variable [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]

/-- Integer shifts preserve and reflect the zero object. -/
theorem isZero_shift_iff (X : C) (n : ℤ) : IsZero (X⟦n⟧) ↔ IsZero X := by
  constructor
  · exact IsZero.of_full_of_faithful_of_isZero (shiftFunctor C n) X
  · intro h
    apply (IsZero.iff_id_eq_zero _).mpr
    rw [← (shiftFunctor C n).map_id, h.eq_zero_of_src (𝟙 X), Functor.map_zero]

variable [HasFiniteBiproducts C]

/-- The q=0 summand always occurs once, so the binomial expansion detects zero. -/
theorem binomialObject_isZero_iff (b d : ℤ) (j : ℕ) (X : C) :
    IsZero (binomialObject b d j X) ↔ IsZero X := by
  unfold binomialObject
  rw [isZero_biproduct_iff]
  simp only [isZero_biproduct_iff, isZero_shift_iff]
  constructor
  · intro h
    exact h ⟨0, Nat.succ_pos j⟩ ⟨0, by simp⟩
  · intro h _ _
    exact h

variable [HasBinaryBiproducts C]
variable {S : Type w} (Phi : C ⥤ C) [Phi.Additive] [Phi.CommShift ℤ]
  (M : S → C) (H : S → S) (b d : ℤ)

/-- Exact zero detection for the iterates; no faithfulness of M is silently assumed. -/
theorem iteration_isZero_iff
    (split : ∀ Y, Phi.obj (M Y) ≅ (M (H Y))⟦b⟧ ⊞ (M (H Y))⟦b+d⟧)
    (j : ℕ) (Y : S) :
    IsZero ((Phi.obj^[j]) (M Y)) ↔ IsZero (M ((H^[j]) Y)) :=
  (binomialIteration Phi M H b d split j Y).isZero_iff.trans
    (binomialObject_isZero_iff b d j _)

theorem iteration_nonzero_iff
    (split : ∀ Y, Phi.obj (M Y) ≅ (M (H Y))⟦b⟧ ⊞ (M (H Y))⟦b+d⟧)
    (j : ℕ) (Y : S) :
    ¬ IsZero ((Phi.obj^[j]) (M Y)) ↔ ¬ IsZero (M ((H^[j]) Y)) :=
  not_congr (iteration_isZero_iff Phi M H b d split j Y)
end ExternalTensor.Binomial

end

end OAI
