import OAI.Algebra.AuslanderReiten.Ext.ExternalComplexIso
import OAI.Algebra.AuslanderReiten.Ext.ExternalCubicInclusion

namespace OAI

noncomputable section
namespace ArExplicit.ExternalTensor
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable {P P' : ChainComplex (ModuleCat.{u} A) ℕ}
  {Q Q' : ChainComplex (ModuleCat.{u} B) ℕ}
variable (f : P ⟶ P') (g : Q ⟶ Q')
variable (p : ∀ n, P.X (n+3) ⟶ P.X n) (p' : ∀ n, P'.X (n+3) ⟶ P'.X n)
variable (r : ∀ n, Q.X (n+3) ⟶ Q.X n) (r' : ∀ n, Q'.X (n+3) ⟶ Q'.X n)

theorem firstCubic_complexMap
    (hp : ∀ n, p n ≫ f.f n = f.f (n+3) ≫ p' n) (n : ℕ) :
    ModuleCat.ofHom (firstCubic k A B P Q p n) ≫ (complexMap k A B f g).f n =
      (complexMap k A B f g).f (n+3) ≫ ModuleCat.ofHom (firstCubic k A B P' Q' p' n) := by
  apply hom_ext k A B P Q
  intro i j hij
  erw [← Category.assoc, inclusion_firstCubic k A B P Q p i j n hij,
    ← Category.assoc, inclusion_complexMap k A B f g i j (n+3) hij,
    Category.assoc, inclusion_firstCubic k A B P' Q' p' i j n hij]
  by_cases hi : i<3
  · have hi : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases hi with rfl | rfl | rfl <;> change (0 : _ ⟶ _) ≫ _ = _ ≫ (0 : _ ⟶ _)
    all_goals simp only [zero_comp, comp_zero]
  · obtain ⟨a,ha⟩ : ∃ a, i=a+3 := ⟨i-3, by omega⟩
    subst i
    erw [firstCubicEntry_high k A B P Q p a j n hij,
      firstCubicEntry_high k A B P' Q' p' a j n hij,
      Category.assoc, inclusion_complexMap k A B f g a j n (by omega),
      ← Category.assoc, ← Category.assoc,
      ← mapHom_comp k A B (p a) (f.f a) (𝟙 (Q.X j)) (g.f j),
      ← mapHom_comp k A B (f.f (a+3)) (p' a) (g.f j) (𝟙 (Q'.X j)),
      Category.id_comp]
    simpa only [Category.comp_id] using congrArg
      (fun z => mapHom k A B z (g.f j) ≫ inclusion k A B P' Q' a j n (by omega)) (hp a)

theorem secondCubic_complexMap
    (hr : ∀ n, r n ≫ g.f n = g.f (n+3) ≫ r' n) (n : ℕ) :
    ModuleCat.ofHom (secondCubic k A B P Q r n) ≫ (complexMap k A B f g).f n =
      (complexMap k A B f g).f (n+3) ≫ ModuleCat.ofHom (secondCubic k A B P' Q' r' n) := by
  apply hom_ext k A B P Q
  intro i j hij
  erw [← Category.assoc, inclusion_secondCubic k A B P Q r i j n hij,
    ← Category.assoc, inclusion_complexMap k A B f g i j (n+3) hij,
    Category.assoc, inclusion_secondCubic k A B P' Q' r' i j n hij]
  by_cases hj : j<3
  · have hj : j=0 ∨ j=1 ∨ j=2 := by omega
    rcases hj with rfl | rfl | rfl <;> change (0 : _ ⟶ _) ≫ _ = _ ≫ (0 : _ ⟶ _)
    all_goals simp only [zero_comp, comp_zero]
  · obtain ⟨a,ha⟩ : ∃ a, j=a+3 := ⟨j-3, by omega⟩
    subst j
    erw [secondCubicEntry_high k A B P Q r i a n hij,
      secondCubicEntry_high k A B P' Q' r' i a n hij,
      Category.assoc, inclusion_complexMap k A B f g i a n (by omega),
      ← Category.assoc, ← Category.assoc,
      ← mapHom_comp k A B (𝟙 (P.X i)) (f.f i) (r a) (g.f a),
      ← mapHom_comp k A B (f.f i) (𝟙 (P'.X i)) (g.f (a+3)) (r' a),
      Category.id_comp]
    simpa only [Category.comp_id] using congrArg
      (fun z => mapHom k A B (f.f i) z ≫ inclusion k A B P' Q' i a n (by omega)) (hr a)

end ArExplicit.ExternalTensor

end

end OAI
