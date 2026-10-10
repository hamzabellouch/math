import OAI.Algebra.Finitistic.Bar.BarFunctor
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

namespace OAI
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
noncomputable section
namespace DerivedBar
universe u
variable {D : Type u} [Ring D]
local notation "c" => ComplexShape.down ℕ

/-- Each diagonal of a first-quadrant total complex is finite. -/
instance finiteTotalDiagonal (n : ℕ) : Finite ((ComplexShape.π c c c) ⁻¹' {n}) := by
  apply Finite.of_injective (fun p => (⟨p.val.1, show p.val.1 < n+1 by
    have := p.property; change p.val.1+p.val.2=n at this; omega⟩ : Fin (n+1)))
  intro a b h
  apply Subtype.ext
  have hab := congrArg Fin.val h
  change a.val.1=b.val.1 at hab
  have ha := a.property
  have hb := b.property
  change a.val.1+a.val.2=n at ha
  change b.val.1+b.val.2=n at hb
  exact Prod.ext hab (by omega)

noncomputable instance fintypeTotalDiagonal (n : ℕ) :
    Fintype ((ComplexShape.π c c c) ⁻¹' {n}) := Fintype.ofFinite _

variable (G : ModuleCat.{u} D ⥤ ModuleCat.{u} D) [G.Additive]
variable (K : HomologicalComplex₂ (ModuleCat.{u} D) c c)

abbrev mapBicomplex : HomologicalComplex₂ (ModuleCat.{u} D) c c :=
  ((G.mapHomologicalComplex c).mapHomologicalComplex c).obj K

/-- Maps out of the image of a total term, using only a finite coproduct. -/
def totalMapDesc {n : ℕ} {Y : ModuleCat.{u} D}
    (f : ∀ i q (_ : i+q=n), G.obj ((K.X i).X q) ⟶ Y) :
    G.obj ((K.total c).X n) ⟶ Y :=
  (isColimitOfPreserves G (K.toGradedObject.isColimitCofanMapObj
    (ComplexShape.π c c c) n)).desc
    { pt := Y
      ι := Discrete.natTrans (fun j => f j.as.val.1 j.as.val.2 j.as.property) }

@[reassoc (attr := simp)]
theorem ι_totalMapDesc {n : ℕ} {Y : ModuleCat.{u} D}
    (f : ∀ i q (_ : i+q=n), G.obj ((K.X i).X q) ⟶ Y)
    (i q : ℕ) (h : i+q=n) :
    G.map (K.ιTotal c i q n h) ≫ totalMapDesc G K f = f i q h := by
  exact (isColimitOfPreserves G (K.toGradedObject.isColimitCofanMapObj
    (ComplexShape.π c c c) n)).fac _ ⟨⟨⟨i,q⟩,h⟩⟩

theorem totalMap_hom_ext {n : ℕ} {Y : ModuleCat.{u} D}
    {f g : G.obj ((K.total c).X n) ⟶ Y}
    (h : ∀ i q (hi : i+q=n),
      G.map (K.ιTotal c i q n hi) ≫ f = G.map (K.ιTotal c i q n hi) ≫ g) : f=g := by
  apply IsColimit.hom_ext
    (isColimitOfPreserves G (K.toGradedObject.isColimitCofanMapObj
      (ComplexShape.π c c c) n))
  rintro ⟨⟨⟨i,q⟩,hi⟩⟩
  exact h i q hi

/-- Additive functors commute with each finite diagonal sum. -/
def totalMapIsoX (n : ℕ) :
    G.obj ((K.total c).X n) ≅ ((mapBicomplex G K).total c).X n where
  hom := totalMapDesc G K (fun i q h => (mapBicomplex G K).ιTotal c i q n h)
  inv := (mapBicomplex G K).totalDesc (fun i q h => G.map (K.ιTotal c i q n h))
  hom_inv_id := by apply totalMap_hom_ext G K; intros; simp
  inv_hom_id := by apply HomologicalComplex₂.total.hom_ext; intros; simp

@[reassoc (attr := simp)]
theorem ι_totalMapIsoX_inv (i q n : ℕ) (h : i+q=n) :
    (mapBicomplex G K).ιTotal c i q n h ≫ (totalMapIsoX G K n).inv =
      G.map (K.ιTotal c i q n h) := by
  simp [totalMapIsoX]

theorem ιTotalOrZero_totalMapIsoX_inv (i q n : ℕ) :
    (mapBicomplex G K).ιTotalOrZero c i q n ≫ (totalMapIsoX G K n).inv =
      G.map (K.ιTotalOrZero c i q n) := by
  by_cases h : i+q=n
  · rw [HomologicalComplex₂.ιTotalOrZero_eq _ _ _ _ _ h,
      HomologicalComplex₂.ιTotalOrZero_eq _ _ _ _ _ h, ι_totalMapIsoX_inv]
  · rw [HomologicalComplex₂.ιTotalOrZero_eq_zero _ _ _ _ _ h,
      HomologicalComplex₂.ιTotalOrZero_eq_zero _ _ _ _ _ h, zero_comp, G.map_zero]

theorem d₁_totalMapIsoX_inv (i q n : ℕ) :
    (mapBicomplex G K).d₁ c i q n ≫ (totalMapIsoX G K n).inv =
      G.map (K.d₁ c i q n) := by
  by_cases h : (c).Rel i ((c).next i)
  · rw [HomologicalComplex₂.d₁_eq' _ _ h, HomologicalComplex₂.d₁_eq' _ _ h]
    simp only [Units.smul_def, zsmul_comp, Category.assoc,
      ιTotalOrZero_totalMapIsoX_inv, Units.smul_def, G.map_zsmul, G.map_comp]
    rfl
  · rw [HomologicalComplex₂.d₁_eq_zero _ _ _ _ _ h,
      HomologicalComplex₂.d₁_eq_zero _ _ _ _ _ h, zero_comp, G.map_zero]

theorem d₂_totalMapIsoX_inv (i q n : ℕ) :
    (mapBicomplex G K).d₂ c i q n ≫ (totalMapIsoX G K n).inv =
      G.map (K.d₂ c i q n) := by
  by_cases h : (c).Rel q ((c).next q)
  · rw [HomologicalComplex₂.d₂_eq' _ _ _ h, HomologicalComplex₂.d₂_eq' _ _ _ h]
    simp only [Units.smul_def, zsmul_comp, Category.assoc,
      ιTotalOrZero_totalMapIsoX_inv, Units.smul_def, G.map_zsmul, G.map_comp]
    rfl
  · rw [HomologicalComplex₂.d₂_eq_zero _ _ _ _ _ h,
      HomologicalComplex₂.d₂_eq_zero _ _ _ _ _ h, zero_comp, G.map_zero]

/-- Additive functors commute with first-quadrant totalization as chain complexes,
with the actual horizontal and signed vertical differential. -/
def totalMapIso : (G.mapHomologicalComplex c).obj (K.total c) ≅
    (mapBicomplex G K).total c :=
  (HomologicalComplex.Hom.isoOfComponents (fun n => (totalMapIsoX G K n).symm)
    (by
      intro i j hij
      apply HomologicalComplex₂.total.hom_ext
      intro a b h
      change (mapBicomplex G K).ιTotal c a b i h ≫ (totalMapIsoX G K i).inv ≫
          G.map ((K.total c).d i j) =
        (mapBicomplex G K).ιTotal c a b i h ≫
          ((mapBicomplex G K).total c).d i j ≫ (totalMapIsoX G K j).inv
      rw [ι_totalMapIsoX_inv_assoc, ← G.map_comp]
      simp only [HomologicalComplex₂.total_d, comp_add, add_comp,
        HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂,
        HomologicalComplex₂.ι_D₁_assoc, HomologicalComplex₂.ι_D₂_assoc,
        G.map_add, d₁_totalMapIsoX_inv, d₂_totalMapIsoX_inv])).symm
end DerivedBar

end

end OAI
