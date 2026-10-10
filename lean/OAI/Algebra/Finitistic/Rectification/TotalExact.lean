import OAI.Algebra.Finitistic.Rectification.TotalFunctorial
import OAI.Algebra.Finitistic.Rectification.ExactProducts
import Mathlib.Algebra.Category.ModuleCat.Biproducts

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
noncomputable section
namespace LittleFinitistic.RectificationTotal
universe u
variable {S : Type u} [Ring S]

/-- The canonical binary sum/product identification respects the supplied maps. -/
theorem prodIso_naturality {X Y X' Y' : ModuleCat.{u} S} (f : X ⟶ X') (g : Y ⟶ Y') :
    biprod.map f g ≫ (ModuleCat.biprodIsoProd X' Y').hom =
      (ModuleCat.biprodIsoProd X Y).hom ≫ ModuleCat.ofHom (f.hom.prodMap g.hom) := by
  apply (cancel_epi (ModuleCat.biprodIsoProd X Y).inv).1
  apply (cancel_mono (ModuleCat.biprodIsoProd X' Y').inv).1
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc]
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.map_fst, ModuleCat.biprodIsoProd_inv_comp_fst]
    rw [← Category.assoc, ModuleCat.biprodIsoProd_inv_comp_fst]
    rfl
  · simp only [Category.assoc, biprod.map_snd, ModuleCat.biprodIsoProd_inv_comp_snd]
    rw [← Category.assoc, ModuleCat.biprodIsoProd_inv_comp_snd]
    rfl

variable {L₀ L₁ L₂ M₀ M₁ M₂ N₀ N₁ N₂ : CochainComplex (ModuleCat.{u} S) ℤ}
variable {p : L₁ ⟶ L₀} {q : L₂ ⟶ L₁} {h : Homotopy (q ≫ p) 0}
variable {p' : M₁ ⟶ M₀} {q' : M₂ ⟶ M₁} {h' : Homotopy (q' ≫ p') 0}
variable {p'' : N₁ ⟶ N₀} {q'' : N₂ ⟶ N₁} {h'' : Homotopy (q'' ≫ p'') 0}

/-- The native total's term as the actual product of the three input modules. -/
def totalTermIso (p : L₁ ⟶ L₀) (q : L₂ ⟶ L₁) (h : Homotopy (q ≫ p) 0) (n : ℤ) :
    (total p q h).X n ≅ ModuleCat.of S ((L₂.X (n+2) × L₁.X (n+1)) × L₀.X n) :=
  termIso p q h n ≪≫
    biprod.mapIso (ModuleCat.biprodIsoProd _ _) (Iso.refl _) ≪≫
    ModuleCat.biprodIsoProd _ _

namespace MapData
variable (a : MapData p q h p' q' h')

/-- The explicit total map acts componentwise in the concrete term product. -/
theorem totalMap_product (n : ℤ) :
    a.totalMap.f n ≫ (totalTermIso p' q' h' n).hom =
      (totalTermIso p q h n).hom ≫ ModuleCat.ofHom
        (((a.f₂.f (n+2)).hom.prodMap (a.f₁.f (n+1)).hom).prodMap (a.f₀.f n).hom) := by
  have hb :
      biprod.map (biprod.map (a.f₂.f (n+2)) (a.f₁.f (n+1))) (a.f₀.f n) ≫
        biprod.map (ModuleCat.biprodIsoProd (M₂.X (n+2)) (M₁.X (n+1))).hom (𝟙 (M₀.X n)) =
      biprod.map (ModuleCat.biprodIsoProd (L₂.X (n+2)) (L₁.X (n+1))).hom (𝟙 (L₀.X n)) ≫
        biprod.map (ModuleCat.ofHom ((a.f₂.f (n+2)).hom.prodMap (a.f₁.f (n+1)).hom)) (a.f₀.f n) := by
    rw [biprodMap_comp, biprodMap_comp, Category.comp_id, Category.id_comp,
      prodIso_naturality]
  dsimp only [totalTermIso, Iso.trans_hom, biprod.mapIso_hom, Iso.refl_hom]
  rw [← Category.assoc, a.totalMap_term]
  simp only [Category.assoc]
  erw [biprod.mapIso_hom, biprod.mapIso_hom, Iso.refl_hom, Iso.refl_hom]
  rw [reassoc_of% hb]
  rw [prodIso_naturality]

/-- A short exact triple of column maps induces short exactness of the actual
supplied total maps, retaining the inclusion and quotient maps themselves. -/
theorem totalMap_shortExact (b : MapData p' q' h' p'' q'' h'')
    (ex₀ : ∀ n, Function.Exact (a.f₀.f n) (b.f₀.f n))
    (ex₁ : ∀ n, Function.Exact (a.f₁.f n) (b.f₁.f n))
    (ex₂ : ∀ n, Function.Exact (a.f₂.f n) (b.f₂.f n))
    (inj₀ : ∀ n, Function.Injective (a.f₀.f n))
    (inj₁ : ∀ n, Function.Injective (a.f₁.f n))
    (inj₂ : ∀ n, Function.Injective (a.f₂.f n))
    (surj₀ : ∀ n, Function.Surjective (b.f₀.f n))
    (surj₁ : ∀ n, Function.Surjective (b.f₁.f n))
    (surj₂ : ∀ n, Function.Surjective (b.f₂.f n)) (n : ℤ) :
    Function.Injective (a.totalMap.f n) ∧
      Function.Exact (a.totalMap.f n) (b.totalMap.f n) ∧
      Function.Surjective (b.totalMap.f n) := by
  let inner := shortExact_prod (ex₂ (n+2)) (ex₁ (n+1))
    (inj₂ (n+2)) (inj₁ (n+1)) (surj₂ (n+2)) (surj₁ (n+1))
  let all := shortExact_prod inner.2.1 (ex₀ n) inner.1 (inj₀ n) inner.2.2 (surj₀ n)
  apply shortExact_transport (totalTermIso p q h n).toLinearEquiv.toEquiv
    (totalTermIso p' q' h' n).toLinearEquiv.toEquiv
    (totalTermIso p'' q'' h'' n).toLinearEquiv.toEquiv (by simp)
    (fun x => congrArg (fun f => f x) (a.totalMap_product n))
    (fun x => congrArg (fun f => f x) (b.totalMap_product n)) all.1 all.2.1 all.2.2
end MapData
end LittleFinitistic.RectificationTotal

end

end OAI
