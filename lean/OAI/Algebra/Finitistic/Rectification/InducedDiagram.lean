import OAI.Algebra.Finitistic.Rectification.DiagramAssembly
import Mathlib.CategoryTheory.Preadditive.Biproducts

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
noncomputable section
namespace ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
instance biFiniteBiproducts : HasFiniteBiproducts (BiComplex k B) :=
  HasFiniteBiproducts.of_hasFiniteProducts
instance biBinaryBiproducts : HasBinaryBiproducts (BiComplex k B) :=
  HasBinaryBiproducts.of_hasBinaryProducts

private theorem smul_comp_add {C : Type*} [Category C] [Preadditive C] [Linear k C]
    {X Y₁ Y₂ Z : C} (c : k) (f₁ : X ⟶ Y₁) (f₂ : Y₁ ⟶ Z)
    (g₁ : X ⟶ Y₂) (g₂ : Y₂ ⟶ Z) :
    (c • f₁) ≫ f₂ + (c • g₁) ≫ g₂ = c • (f₁ ≫ f₂ + g₁ ≫ g₂) := by
  simp only [Linear.smul_comp, smul_add]

private def framedMapHomotopy {C E : Type*} [Category C] [Preadditive C]
    [Category E] [Preadditive E] (G : C ⥤ E) [G.Additive]
    {X Y : CochainComplex C ℤ} {P Q : CochainComplex E ℤ}
    (f : X ⟶ Y) (H : Homotopy f 0)
    (a : P ⟶ (G.mapHomologicalComplex (.up ℤ)).obj X)
    (b : (G.mapHomologicalComplex (.up ℤ)).obj Y ⟶ Q) :
    Homotopy (a ≫ (G.mapHomologicalComplex (.up ℤ)).map f ≫ b) 0 where
  hom i j := a.f i ≫ G.map (H.hom i j) ≫ b.f j
  zero i j hij := by rw [H.zero i j hij, G.map_zero, zero_comp, comp_zero]
  comm i := by
    let h := ((G.mapHomotopy H).compLeft a).compRight b
    simpa [h, Category.assoc, dNext, prevD] using h.comm i

variable {A J R : Type} [Fintype A] [Fintype J] [Fintype R]

/-- Only the finite quadratic diagram data used in the column calculation.
These equations hold for Section 3's arrows in e_j B e_i and relation basis.
No independence of relations is needed for the stronger assembly statement. -/
structure Quadratic where
  e₀ : B
  e₁ : B
  e₂ : B
  a : A → B
  b : J → B
  ha : ∀ i, a i * e₀ = a i
  hb : ∀ j, b j * e₁ = b j
  coeff : R → A → J → k
  relation : ∀ r, ∑ i, ∑ j, coeff r i j • (b j * a i) = 0

variable {k B}
variable (s : Quadratic k B (A := A) (J := J) (R := R))
variable (D₀ D₁ D₂ : RightComplex B)
variable (f : A → (D₀ ⟶ D₁)) (g : J → (D₁ ⟶ D₂))

/-- The actual finite relation evaluated on the chosen chain maps. -/
def relationMap (r : R) : D₀ ⟶ D₂ := ∑ a, ∑ b, s.coeff r a b • (f a ≫ g b)

/-- All columns and components are induced from actual modules, paths and maps. -/
def inducedData : AssemblyData (C := BiComplex k B) (A := A) (J := J) (R := R) where
  V₀ := (columnComplex k B s.e₀).obj D₀
  V₁ := (columnComplex k B s.e₁).obj D₁
  V₂ := (columnComplex k B s.e₂).obj D₂
  U _ := (columnComplex k B s.e₁).obj D₀
  V _ := (columnComplex k B s.e₂).obj D₁
  W _ := (columnComplex k B s.e₂).obj D₀
  pa₀ a := path k B s.e₀ s.e₁ (s.a a) (s.ha a) D₀
  pa₁ a := (columnComplex k B s.e₁).map (f a)
  pb₁ b := path k B s.e₁ s.e₂ (s.b b) (s.hb b) D₁
  pb₂ b := (columnComplex k B s.e₂).map (g b)
  qa r a b := s.coeff r a b • path k B s.e₁ s.e₂ (s.b b) (s.hb b) D₀
  qb r a b := s.coeff r a b • (columnComplex k B s.e₂).map (f a)
  rel r := (columnComplex k B s.e₂).map (relationMap s D₀ D₁ D₂ f g r)
  middle r a b := by simp [Linear.smul_comp]
  first r := by
    simpa only [Linear.smul_comp] using
      paths_relation k B s.e₀ s.e₁ s.e₂ s.a s.b s.ha s.hb (s.coeff r) (s.relation r) D₀
  last r := by
    simp only [Linear.smul_comp, relationMap, Functor.map_sum, Functor.map_smul,
      Functor.map_comp]

abbrev L0Prime := (inducedData s D₀ D₁ D₂ f g).L₀
abbrev L1Prime := (inducedData s D₀ D₁ D₂ f g).L₁
abbrev L2Prime := (inducedData s D₀ D₁ D₂ f g).L₂
abbrev p := (inducedData s D₀ D₁ D₂ f g).p
abbrev q := (inducedData s D₀ D₁ D₂ f g).q

omit [Fintype R] in
@[reassoc] theorem p_arrow01 (a : A) :
    biproduct.ι (inducedData s D₀ D₁ D₂ f g).U a ≫ biprod.inl ≫
      p s D₀ D₁ D₂ f g =
    path k B s.e₀ s.e₁ (s.a a) (s.ha a) D₀ ≫ (inducedData s D₀ D₁ D₂ f g).in₀ -
      (columnComplex k B s.e₁).map (f a) ≫ (inducedData s D₀ D₁ D₂ f g).in₁ := by
  simp only [p, AssemblyData.p, biprod.inl_desc, biproduct.ι_desc]
  rfl

omit [Fintype R] in
@[reassoc] theorem p_arrow12 (b : J) :
    biproduct.ι (inducedData s D₀ D₁ D₂ f g).V b ≫ biprod.inr ≫
      p s D₀ D₁ D₂ f g =
    path k B s.e₁ s.e₂ (s.b b) (s.hb b) D₁ ≫ (inducedData s D₀ D₁ D₂ f g).in₁ -
      (columnComplex k B s.e₂).map (g b) ≫ (inducedData s D₀ D₁ D₂ f g).in₂ := by
  simp only [p, AssemblyData.p, biprod.inr_desc, biproduct.ι_desc]
  rfl

theorem q_relation (r : R) :
    biproduct.ι (inducedData s D₀ D₁ D₂ f g).W r ≫ q s D₀ D₁ D₂ f g =
    ∑ a, ∑ b, s.coeff r a b •
      (path k B s.e₁ s.e₂ (s.b b) (s.hb b) D₀ ≫
        biproduct.ι (inducedData s D₀ D₁ D₂ f g).U a ≫ biprod.inl +
       (columnComplex k B s.e₂).map (f a) ≫
        biproduct.ι (inducedData s D₀ D₁ D₂ f g).V b ≫ biprod.inr) := by
  simp only [q, AssemblyData.q, biproduct.ι_desc]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  exact smul_comp_add k (s.coeff r a b) _ _ _ _

variable (H : ∀ r, Homotopy (relationMap s D₀ D₁ D₂ f g r) 0)

/-- Positive degree-minus-one h of the manuscript, packaged with its equation. -/
def positiveHomotopy :
    Homotopy (biproduct.desc fun r =>
      (inducedData s D₀ D₁ D₂ f g).rel r ≫ (inducedData s D₀ D₁ D₂ f g).in₂) 0 := by
  classical
  let t := inducedData s D₀ D₁ D₂ f g
  let F (r : R) := biproduct.π t.W r ≫ t.rel r ≫ t.in₂
  let hh (r : R) : Homotopy (F r) 0 :=
    framedMapHomotopy (columnFunctor k B s.e₂) (relationMap s D₀ D₁ D₂ f g r)
      (H r) (biproduct.π t.W r) t.in₂
  have hs := AssemblyData.sumHomotopy F hh
  have heq : (∑ r, F r) = biproduct.desc (fun r => t.rel r ≫ t.in₂) := by
    exact biproduct.desc_eq.symm
  refine { hom := hs.hom, zero := hs.zero, comm := ?_ }
  intro i
  rw [← heq]
  exact hs.comm i

/-- The sign-correct null-homotopy required by RectificationTotal.total. -/
def nullHomotopy : Homotopy (q s D₀ D₁ D₂ f g ≫ p s D₀ D₁ D₂ f g) 0 := by
  rw [AssemblyData.composite]
  simpa using (positiveHomotopy s D₀ D₁ D₂ f g H).smul (-1 : k)

/-- The manuscript h, with zero components away from degree minus one. -/
def h (i j : ℤ) := (positiveHomotopy s D₀ D₁ D₂ f g H).hom i j

theorem h_formula (i j : ℤ) : h s D₀ D₁ D₂ f g H i j =
    ∑ r, (biproduct.π (inducedData s D₀ D₁ D₂ f g).W r).f i ≫
      (columnFunctor k B s.e₂).map ((H r).hom i j) ≫
      (inducedData s D₀ D₁ D₂ f g).in₂.f j := rfl

theorem h_relation (r : R) (i j : ℤ) :
    (biproduct.ι (inducedData s D₀ D₁ D₂ f g).W r).f i ≫ h s D₀ D₁ D₂ f g H i j =
    (columnFunctor k B s.e₂).map ((H r).hom i j) ≫
      (inducedData s D₀ D₁ D₂ f g).in₂.f j := by
  classical
  simp only [h_formula, Preadditive.comp_sum, ← Category.assoc, ← comp_f]
  simp only [biproduct.ι_π]
  rw [Finset.sum_eq_single r]
  · simp
    rfl
  · intro x _ hxr
    simp [Ne.symm hxr]
  · simp

theorem h_shape (i j : ℤ) (hij : j + 1 ≠ i) : h s D₀ D₁ D₂ f g H i j = 0 :=
  (positiveHomotopy s D₀ D₁ D₂ f g H).zero i j hij

/-- Precisely the remaining off-diagonal entry in the manuscript's d_P squared. -/
theorem square (n : ℤ) :
    h s D₀ D₁ D₂ f g H n (n-1) ≫ (L0Prime s D₀ D₁ D₂ f g).d (n-1) n +
    (q s D₀ D₁ D₂ f g ≫ p s D₀ D₁ D₂ f g).f n +
    (L2Prime s D₀ D₁ D₂ f g).d n (n+1) ≫ h s D₀ D₁ D₂ f g H (n+1) n = 0 := by
  have hh := (positiveHomotopy s D₀ D₁ D₂ f g H).comm n
  rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel n (n+1) by simp),
    prevD_eq _ (show (ComplexShape.up ℤ).Rel (n-1) n by simp)] at hh
  rw [AssemblyData.composite, neg_f_apply, hh]
  dsimp [h, L0Prime, L2Prime]
  abel
end ExternalTensor.Section4

end

end OAI
