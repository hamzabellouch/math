import Mathlib.CategoryTheory.Linear.Basic
import OAI.Algebra.Finitistic.Encoding.QuadraticEncoding
import OAI.Algebra.Finitistic.Encoding.QuadraticPresentation

namespace OAI

namespace LittleFinitistic.QuotientAction
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Preadditive
open QuadraticEncoding

variable {k : Type*} [Field k] {C : Type*} [Category C] [Preadditive C] [Linear k C]
variable {X₀ X₁ X₂ : C} {d t : ℕ} (P : Relations k d t)
  (s : X₀ ⟶ X₁) (s' : X₁ ⟶ X₂) [IsIso s] [IsIso s']
  (a : Fin d → (X₀ ⟶ X₁)) (b : Fin d → (X₁ ⟶ X₂))
  (hc : ∀ h, s ≫ b h = a h ≫ s')

noncomputable def normalized (h : Fin d) : End X₀ := a h ≫ inv s

include hc in
omit [Preadditive C] [IsIso s'] in
lemma normalized_product_comp (h l : Fin d) :
    (normalized s a h * normalized s a l) ≫ s ≫ s' = a l ≫ b h := by
  simp only [normalized,End.mul_def,assoc,IsIso.inv_hom_id_assoc]
  rw [← hc h]
  simp only [IsIso.inv_hom_id_assoc]

omit [Preadditive C] [IsIso s'] in
lemma normalized_comp (h : Fin d) : normalized s a h ≫ s ≫ s' = a h ≫ s' := by
  simp [normalized]

variable (hr : ∀ j,
    (∑ h, ∑ l, P.quadratic j h l • (a l ≫ b h)) +
    (∑ h, P.linear j h • (a h ≫ s')) + P.constant j • (s ≫ s') = 0)

include hc hr in
/-- Normalizing the invertible arrows recovers the original quadratic equations. -/
theorem normalized_relations (j : Fin t) :
    (∑ h, ∑ l, P.quadratic j h l • (normalized s a h * normalized s a l)) +
    (∑ h, P.linear j h • normalized s a h) + P.constant j • (1 : End X₀) = 0 := by
  apply (cancel_mono (s ≫ s')).mp
  dsimp only [End]
  simp only [Preadditive.add_comp,Preadditive.sum_comp,Linear.smul_comp,End.one_def,id_comp,zero_comp]
  simpa only [← End.mul_def,normalized_product_comp s s' a b hc,normalized_comp] using hr j

/-- The degree-at-most-two defining polynomial with the displayed coefficients. -/
def polynomial (j : Fin t) : FreeAlgebra k (Fin d) :=
  (∑ h, ∑ l, P.quadratic j h l • (FreeAlgebra.ι k h * FreeAlgebra.ι k l)) +
  (∑ h, P.linear j h • FreeAlgebra.ι k h) + P.constant j • 1

noncomputable def freeAction : FreeAlgebra k (Fin d) →ₐ[k] End X₀ :=
  FreeAlgebra.lift k (normalized s a)

include hc hr in
lemma freeAction_polynomial (j : Fin t) : freeAction s a (polynomial P j) = 0 := by
  simpa only [freeAction,polynomial,map_add,map_sum,map_smul,map_mul,map_one,
    FreeAlgebra.lift_ι_apply] using normalized_relations P s s' a b hc hr j

/-- The genuine quotient action theta, obtained by descending the free action. -/
noncomputable def quotientAction :
    QuadraticPresentation.Original k (Fin d) (polynomial P) →ₐ[k] End X₀ :=
  (QuadraticPresentation.original k (Fin d) (polynomial P)).liftₐ (freeAction s a)
    (RingCon.ringConGen_le.mpr (by
      rintro x y ⟨j,rfl,rfl⟩
      change freeAction s a (polynomial P j) = freeAction s a 0
      rw [map_zero,freeAction_polynomial P s s' a b hc hr]))

@[simp] theorem quotientAction_generator (h : Fin d) :
    quotientAction P s s' a b hc hr
      (QuadraticPresentation.originalMap k (Fin d) (polynomial P) (FreeAlgebra.ι k h)) =
      normalized s a h := by
  simp [quotientAction,QuadraticPresentation.originalMap,freeAction]

/-- Transport the descended action through the actual presentation equivalence. -/
noncomputable def presentedAction {R : Type*} [Ring R] [Algebra k R]
    (E : QuadraticPresentation.Original k (Fin d) (polynomial P) ≃ₐ[k] R) :
    R →ₐ[k] End X₀ := (quotientAction P s s' a b hc hr).comp E.symm.toAlgHom

omit [Preadditive C] in
/-- Evaluation of normalized generators, with the natural vertex identifications. -/
theorem normalized_evaluation {D : Type*} [Category D] (F : C ⥤ D)
    {Y : D} (e₀ : F.obj X₀ ≅ Y) (e₁ : F.obj X₁ ≅ Y)
    (x : Fin d → (Y ⟶ Y))
    (hs : F.map s ≫ e₁.hom = e₀.hom)
    (ha : ∀ h, F.map (a h) ≫ e₁.hom = e₀.hom ≫ x h) (h : Fin d) :
    F.map (normalized s a h) ≫ e₀.hom = e₀.hom ≫ x h := by
  have hsi : F.map (inv s) ≫ e₀.hom = e₁.hom := by
    apply (cancel_epi (F.map s)).mp
    rw [← assoc,← F.map_comp,IsIso.hom_inv_id,F.map_id,id_comp,hs]
  change F.map (a h ≫ inv s) ≫ e₀.hom = _
  rw [F.map_comp,assoc,hsi,ha]
end LittleFinitistic.QuotientAction

end OAI
