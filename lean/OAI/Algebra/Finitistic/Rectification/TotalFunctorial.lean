import OAI.Algebra.Finitistic.Rectification.RectificationTotal

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open CochainComplex.HomComplex
noncomputable section
namespace LittleFinitistic.RectificationTotal
variable {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
theorem biprodMap_comp {U V W X Y Z : C} (f : U ⟶ W) (g : V ⟶ X)
    (f' : W ⟶ Y) (g' : X ⟶ Z) :
    biprod.map f g ≫ biprod.map f' g' = biprod.map (f ≫ f') (g ≫ g') := by
  apply biprod.hom_ext <;> simp

variable {A B A' B' A'' B'' : CochainComplex C ℤ}

/-- A strictly commuting square induces the ordinary diagonal map of cones. -/
def coneMap (q : A ⟶ B) (q' : A' ⟶ B') (u : A ⟶ A') (v : B ⟶ B')
    (w : u ≫ q' = q ≫ v) : mappingCone q ⟶ mappingCone q' :=
  homotopyCofiber.mapArrowHom q q' (fun j => ⟨j-1, by simp⟩)
    (Arrow.homMk u v w)

@[reassoc (attr := simp)]
theorem coneMap_inl (q : A ⟶ B) (q' : A' ⟶ B') (u : A ⟶ A') (v : B ⟶ B')
    (w : u ≫ q' = q ≫ v) (i j : ℤ) (hij : i + (-1) = j) :
    (mappingCone.inl q).v i j hij ≫ (coneMap q q' u v w).f j =
      u.f i ≫ (mappingCone.inl q').v i j hij := by
  dsimp [coneMap, homotopyCofiber.mapArrowHom, mappingCone.inl]
  erw [homotopyCofiber.inlX_desc_f]
  simp
  congr 1
  exact homotopyCofiber.inrCompHomotopy_hom q' _ i j (by change j+1=i; omega)

@[reassoc (attr := simp)]
theorem coneMap_inr (q : A ⟶ B) (q' : A' ⟶ B') (u : A ⟶ A') (v : B ⟶ B')
    (w : u ≫ q' = q ≫ v) (i : ℤ) :
    (mappingCone.inr q).f i ≫ (coneMap q q' u v w).f i =
      v.f i ≫ (mappingCone.inr q').f i := by
  dsimp [coneMap, homotopyCofiber.mapArrowHom, mappingCone.inr]
  exact homotopyCofiber.inrX_desc_f _ _ _ _

@[reassoc (attr := simp)]
theorem cone_inl_termIso (q : A ⟶ B) (i j : ℤ) (hij : i+1=j) :
    (mappingCone.inl q).v j i (by omega) ≫ (homotopyCofiber.XIsoBiprod q i j hij).hom =
      biprod.inl :=
  homotopyCofiber.inlX_XIsoBiprod_hom _ _ _ _

@[reassoc (attr := simp)]
theorem cone_inr_termIso (q : A ⟶ B) (i j : ℤ) (hij : i+1=j) :
    (mappingCone.inr q).f i ≫ (homotopyCofiber.XIsoBiprod q i j hij).hom =
      biprod.inr :=
  homotopyCofiber.inrX_XIsoBiprod_hom _ _ _ _

/-- On terms the cone map is exactly the sum of the two supplied maps. -/
theorem coneMap_term (q : A ⟶ B) (q' : A' ⟶ B') (u : A ⟶ A') (v : B ⟶ B')
    (w : u ≫ q' = q ≫ v) (i j : ℤ) (hij : i+1=j) :
    (coneMap q q' u v w).f i ≫ (homotopyCofiber.XIsoBiprod q' i j hij).hom =
      (homotopyCofiber.XIsoBiprod q i j hij).hom ≫ biprod.map (u.f j) (v.f i) := by
  apply mappingCone.ext_from q j i hij
  · erw [coneMap_inl_assoc, cone_inl_termIso, ← Category.assoc, cone_inl_termIso,
      biprod.inl_map]
  · erw [coneMap_inr_assoc, cone_inr_termIso, ← Category.assoc, cone_inr_termIso,
      biprod.inr_map]

@[simp]
theorem coneMap_id (q : A ⟶ B) : coneMap q q (𝟙 A) (𝟙 B) (by simp) = 𝟙 _ := by
  change homotopyCofiber.mapArrowHom q q _ (𝟙 _) = 𝟙 _
  exact homotopyCofiber.mapArrowHom_id _ _

theorem coneMap_comp (q : A ⟶ B) (q' : A' ⟶ B') (q'' : A'' ⟶ B'')
    (u : A ⟶ A') (v : B ⟶ B') (w : u ≫ q' = q ≫ v)
    (u' : A' ⟶ A'') (v' : B' ⟶ B'') (w' : u' ≫ q'' = q' ≫ v') :
    coneMap q q'' (u ≫ u') (v ≫ v') (by rw [Category.assoc, w', ← Category.assoc, w, Category.assoc]) =
      coneMap q q' u v w ≫ coneMap q' q'' u' v' w' := by
  exact homotopyCofiber.mapArrowHom_comp _ _ _ _ (Arrow.homMk u v w) (Arrow.homMk u' v' w')

variable {L₀ L₁ L₂ M₀ M₁ M₂ N₀ N₁ N₂ : CochainComplex C ℤ}
variable {p : L₁ ⟶ L₀} {q : L₂ ⟶ L₁} {h : Homotopy (q ≫ p) 0}
variable {p' : M₁ ⟶ M₀} {q' : M₂ ⟶ M₁} {h' : Homotopy (q' ≫ p') 0}

/-- Morphisms preserve both degree-zero maps and the specified relation
homotopy, which is part of the three-column input data. -/
structure MapData (p : L₁ ⟶ L₀) (q : L₂ ⟶ L₁) (h : Homotopy (q ≫ p) 0)
    (p' : M₁ ⟶ M₀) (q' : M₂ ⟶ M₁) (h' : Homotopy (q' ≫ p') 0) where
  f₀ : L₀ ⟶ M₀
  f₁ : L₁ ⟶ M₁
  f₂ : L₂ ⟶ M₂
  commP : f₁ ≫ p' = p ≫ f₀
  commQ : f₂ ≫ q' = q ≫ f₁
  commH : ∀ i j, f₂.f i ≫ h'.hom i j = h.hom i j ≫ f₀.f j

namespace MapData
variable (a : MapData p q h p' q' h')

def inner : mappingCone q ⟶ mappingCone q' := coneMap q q' a.f₂ a.f₁ a.commQ

theorem rectifyingMap_naturality : a.inner ≫ rectifyingMap p' q' h' =
    rectifyingMap p q h ≫ a.f₀ := by
  ext n
  apply mappingCone.ext_from q (n+1) n rfl
  · simp only [comp_f, inner, coneMap_inl_assoc, rectifyingMap, mappingCone.inl_v_desc_f_assoc,
      mappingCone.inl_v_desc_f]
    exact a.commH (n+1) n
  · simp only [comp_f, inner, coneMap_inr_assoc, rectifyingMap,
      mappingCone.inr_f_desc_f_assoc, mappingCone.inr_f_desc_f]
    exact congrArg (fun f => f.f n) a.commP

/-- The induced chain map of the native primary's actual iterated-cone total. -/
def totalMap : total p q h ⟶ total p' q' h' :=
  coneMap (rectifyingMap p q h) (rectifyingMap p' q' h') a.inner a.f₀
    a.rectifyingMap_naturality

/-- The zero-column inclusion is preserved by the actual induced total map. -/
@[reassoc]
theorem inclusion_totalMap : inclusion p q h ≫ a.totalMap =
    a.f₀ ≫ inclusion p' q' h' := by
  ext n
  exact coneMap_inr _ _ _ _ _ n

/-- The induced total map is the actual diagonal triple under the native
term decomposition, including both cohomological shifts. -/
theorem totalMap_term (n : ℤ) :
    a.totalMap.f n ≫ (termIso p' q' h' n).hom =
      (termIso p q h n).hom ≫
        biprod.map (biprod.map (a.f₂.f (n+2)) (a.f₁.f (n+1))) (a.f₀.f n) := by
  unfold totalMap termIso
  erw [Iso.trans_hom, Iso.trans_hom, biprod.mapIso_hom, biprod.mapIso_hom, Iso.refl_hom, Iso.refl_hom]
  erw [← Category.assoc, coneMap_term]
  erw [Category.assoc, Category.assoc, biprodMap_comp, biprodMap_comp,
    Category.comp_id, Category.id_comp]
  congr 2
  exact coneMap_term q q' a.f₂ a.f₁ a.commQ (n+1) (n+2) (by omega)

def id (p : L₁ ⟶ L₀) (q : L₂ ⟶ L₁) (h : Homotopy (q ≫ p) 0) :
    MapData p q h p q h where
  f₀ := 𝟙 _
  f₁ := 𝟙 _
  f₂ := 𝟙 _
  commP := by simp
  commQ := by simp
  commH := by intros; simp

variable {p'' : N₁ ⟶ N₀} {q'' : N₂ ⟶ N₁} {h'' : Homotopy (q'' ≫ p'') 0}
def comp (b : MapData p' q' h' p'' q'' h'') : MapData p q h p'' q'' h'' where
  f₀ := a.f₀ ≫ b.f₀
  f₁ := a.f₁ ≫ b.f₁
  f₂ := a.f₂ ≫ b.f₂
  commP := by rw [Category.assoc, b.commP, ← Category.assoc, a.commP, Category.assoc]
  commQ := by rw [Category.assoc, b.commQ, ← Category.assoc, a.commQ, Category.assoc]
  commH i j := by
    simp only [comp_f]
    rw [Category.assoc, b.commH, ← Category.assoc, a.commH, Category.assoc]

@[simp] theorem totalMap_id : (id p q h).totalMap = 𝟙 _ := by
  simp [totalMap, inner, id, coneMap_id, total]

theorem totalMap_comp (b : MapData p' q' h' p'' q'' h'') :
    (a.comp b).totalMap = a.totalMap ≫ b.totalMap := by
  have hi : (a.comp b).inner = a.inner ≫ b.inner := coneMap_comp _ _ _ _ _ _ _ _ _
  refine Eq.trans ?_ (coneMap_comp _ _ _ a.inner a.f₀ a.rectifyingMap_naturality
    b.inner b.f₀ b.rectifyingMap_naturality)
  change coneMap _ _ (a.comp b).inner (a.f₀ ≫ b.f₀) _ = _
  congr 1

end MapData
end LittleFinitistic.RectificationTotal

end

end OAI
