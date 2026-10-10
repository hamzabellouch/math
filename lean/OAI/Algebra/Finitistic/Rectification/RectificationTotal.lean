import OAI.Algebra.Finitistic.Localization.ChainRepresentatives

namespace OAI

namespace LittleFinitistic.RectificationTotal
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex HomComplex

variable {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
variable {L₀ L₁ L₂ : CochainComplex C ℤ} (p : L₁ ⟶ L₀) (q : L₂ ⟶ L₁)
  (h : Homotopy (q ≫ p) 0)

/-- The relation null-homotopy extends p over the first cone. -/
noncomputable def rectifyingMap : mappingCone q ⟶ L₀ :=
  mappingCone.desc q (Cochain.ofHomotopy h) p (by simp [δ_ofHomotopy])

/-- A genuine cochain complex rectifying a three-column homotopy diagram.
The cone convention fixes all differential signs; the three-column term
isomorphism is given below. -/
noncomputable def total : CochainComplex C ℤ := mappingCone (rectifyingMap p q h)

/-- The total complex has exactly the three finite columns. -/
noncomputable def termIso (i : ℤ) :
    (total p q h).X i ≅ (L₂.X (i+2) ⊞ L₁.X (i+1)) ⊞ L₀.X i :=
  homotopyCofiber.XIsoBiprod (rectifyingMap p q h) i (i+1) (by simp) ≪≫
    biprod.mapIso (homotopyCofiber.XIsoBiprod q (i+1) (i+2) (by simp; omega)) (Iso.refl _)

@[simp] theorem total_isZero (i : ℤ) :
    IsZero ((total p q h).X i) ↔
      (IsZero (L₂.X (i+2)) ∧ IsZero (L₁.X (i+1))) ∧ IsZero (L₀.X i) := by
  rw [(termIso p q h i).isZero_iff,biprod_isZero_iff,biprod_isZero_iff]

/-- Bounded columns give a bounded actual total complex. -/
theorem total_bounded (lo hi : ℤ)
    (h₀ : ∀ i, i < lo ∨ hi < i → IsZero (L₀.X i))
    (h₁ : ∀ i, i < lo ∨ hi < i → IsZero (L₁.X i))
    (h₂ : ∀ i, i < lo ∨ hi < i → IsZero (L₂.X i)) :
    ∀ i, i < lo-2 ∨ hi < i → IsZero ((total p q h).X i) := by
  intro i hi'
  rw [total_isZero]
  exact ⟨⟨h₂ _ (by omega),h₁ _ (by omega)⟩,h₀ _ (by omega)⟩

/-- Termwise projectivity is preserved by the concrete three-column construction. -/
theorem total_projective (h₀ : ∀ i, Projective (L₀.X i))
    (h₁ : ∀ i, Projective (L₁.X i)) (h₂ : ∀ i, Projective (L₂.X i)) :
    ∀ i, Projective ((total p q h).X i) := by
  intro i
  let := h₀ i
  let := h₁ (i+1)
  let := h₂ (i+2)
  apply Projective.of_iso (termIso p q h i).symm
  infer_instance

/-- The original zero column includes by an actual chain map. -/
noncomputable def inclusion : L₀ ⟶ total p q h := mappingCone.inr (rectifyingMap p q h)

/-- The first-column boundary vanishes by a specified chain homotopy in the total.
For the induced B-arrow columns this is exactly the arrow compatibility homotopy. -/
noncomputable def boundaryHomotopy : Homotopy (p ≫ inclusion p q h) 0 := by
  let f := rectifyingMap p q h
  let H : Homotopy (f ≫ mappingCone.inr f) 0 :=
    (Cochain.equivHomotopy _ _).symm ⟨mappingCone.inl f,by simp⟩
  have H' := H.compLeft (mappingCone.inr q)
  have heq : mappingCone.inr q ≫ f = p := mappingCone.inr_desc _ _ _ _
  rw [← Category.assoc,heq,CategoryTheory.Limits.comp_zero] at H'
  exact H'

variable {D : Type*} [Category D] [Preadditive D] [HasBinaryBiproducts D]

/-- Projectivity after an additive forgetful functor, needed for right projectivity
of a total built in the category of bimodules. -/
theorem total_projective_after (F : C ⥤ D) [F.Additive]
    (h₀ : ∀ i, Projective (F.obj (L₀.X i)))
    (h₁ : ∀ i, Projective (F.obj (L₁.X i)))
    (h₂ : ∀ i, Projective (F.obj (L₂.X i))) :
    ∀ i, Projective (F.obj ((total p q h).X i)) := by
  intro i
  let := h₀ i
  let := h₁ (i+1)
  let := h₂ (i+2)
  let := preservesBinaryBiproducts_of_preservesBiproducts F
  let e := F.mapIso (termIso p q h i) ≪≫ F.mapBiprod _ _ ≪≫
    biprod.mapIso (F.mapBiprod _ _) (Iso.refl _)
  apply Projective.of_iso e.symm
  infer_instance
end LittleFinitistic.RectificationTotal

end OAI
