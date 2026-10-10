import OAI.Algebra.Finitistic.Iteration.BinomialVanishing

namespace OAI
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace ExternalTensor.Binomial
universe v u w
variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
variable {S : Type w} (F : C ⥤ C) [F.Additive] [F.CommShift ℤ]
  (M : S → C) (H : S → S) (b : ℤ)

/-- Section 6's even-iterate formula, for an actual endofunctor and an objectwise two-step split. -/
def evenIteration
    (split : ∀ Y, F.obj (F.obj (M Y)) ≅ (M (H Y))⟦b⟧ ⊞ (M (H Y))⟦b+3⟧)
    (j : ℕ) (Y : S) :
    (F.obj^[2*j]) (M Y) ≅
      ⨁ fun q : Fin (j+1) => ⨁ fun _ : Fin (Nat.choose j q.val) =>
        (M ((H^[j]) Y))⟦(j : ℤ)*b + 3*(q.val : ℤ)⟧ := by
  have he : (F ⋙ F).obj = F.obj ∘ F.obj := rfl
  simpa only [he, binomialObject, Function.iterate_mul, Function.iterate_succ,
    Function.iterate_zero, Function.id_comp, Functor.comp_obj] using
      binomialIteration (F ⋙ F) M H b 3 split j Y

/-- The precise vanishing equivalence behind the main proof's extinction step. -/
theorem evenIteration_isZero_iff
    (split : ∀ Y, F.obj (F.obj (M Y)) ≅ (M (H Y))⟦b⟧ ⊞ (M (H Y))⟦b+3⟧)
    (j : ℕ) (Y : S) :
    IsZero ((F.obj^[2*j]) (M Y)) ↔ IsZero (M ((H^[j]) Y)) :=
  (evenIteration F M H b split j Y).isZero_iff.trans
    (binomialObject_isZero_iff b 3 j _)

/-- Transfer a concrete zero/nonzero pair without assuming M preserves or reflects zero. -/
theorem even_extinction_pair
    (split : ∀ Y, F.obj (F.obj (M Y)) ≅ (M (H Y))⟦b⟧ ⊞ (M (H Y))⟦b+3⟧)
    (m : ℕ) (Y : S)
    (vanishes : IsZero (M ((H^[m+1]) Y)))
    (survives : ¬ IsZero (M ((H^[m]) Y))) :
    IsZero ((F.obj^[2*(m+1)]) (M Y)) ∧ ¬ IsZero ((F.obj^[2*m]) (M Y)) :=
  ⟨(evenIteration_isZero_iff F M H b split (m+1) Y).mpr vanishes,
    fun h => survives ((evenIteration_isZero_iff F M H b split m Y).mp h)⟩
end ExternalTensor.Binomial

end

end OAI
