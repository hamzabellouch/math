import OAI.Algebra.Finitistic.Rectification.ArrowVertex
import OAI.Algebra.Finitistic.Rectification.RectificationTotal
import Mathlib.Algebra.Category.ModuleCat.Biproducts

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
noncomputable section
namespace ExternalTensor.Section4.ArrowVertex
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]

/-- Original insertion through the zero-column inclusion of the actual total. -/
def iota {L₀ L₁ L₂ : BiComplex k B} (p : L₁ ⟶ L₀) (q : L₂ ⟶ L₁)
    (h : Homotopy (q ≫ p) 0) (e : B) (he : e * e = e)
    (D : RightComplex B) (t : (columnComplex k B e).obj D ⟶ L₀) :
    D ⟶ (vertexComplex k B e).obj (LittleFinitistic.RectificationTotal.total p q h) :=
  diagonalComplex k B e he D ≫ (vertexComplex k B e).map
    (t ≫ LittleFinitistic.RectificationTotal.inclusion p q h)

/-- The insertion has exactly the manuscript's diagonal tensor, before any coordinates. -/
@[simp] theorem iota_original {L₀ L₁ L₂ : BiComplex k B}
    (p : L₁ ⟶ L₀) (q : L₂ ⟶ L₁) (h : Homotopy (q ≫ p) 0)
    (e : B) (he : e * e = e) (D : RightComplex B)
    (t : (columnComplex k B e).obj D ⟶ L₀) (n : ℤ) (x : D.X n) :
    (((iota p q h e he D t).f n) x).val =
      ((t ≫ LittleFinitistic.RectificationTotal.inclusion p q h).f n)
        (generator B e ⊗ₜ[k] x) := rfl

/-- The original p-boundary produces compatibility in the actual target vertex. -/
def compatibility {L₀ L₁ L₂ : BiComplex k B} (p : L₁ ⟶ L₀) (q : L₂ ⟶ L₁)
    (h : Homotopy (q ≫ p) 0) (ei ej a : B) (hei : ei * ei = ei)
    (hej : ej * ej = ej) (hai : a * ei = a) (hja : ej * a = a)
    {D E : RightComplex B} (f : D ⟶ E)
    (t : (columnComplex k B ei).obj D ⟶ L₀)
    (u : (columnComplex k B ej).obj E ⟶ L₀)
    (w : (columnComplex k B ej).obj D ⟶ L₁)
    (hw : w ≫ p = path k B ei ej a hai D ≫ t - (columnComplex k B ej).map f ≫ u) :
    Homotopy
      (iota p q h ei hei D t ≫ arrowComplex k B ei ej a hja
        (LittleFinitistic.RectificationTotal.total p q h))
      (f ≫ iota p q h ej hej E u) := by
  let inc := LittleFinitistic.RectificationTotal.inclusion p q h
  let F := vertexComplex k B ej
  have hb := (LittleFinitistic.RectificationTotal.boundaryHomotopy p q h).compLeft w
  have hh := ((vertex k B ej).mapHomotopy hb).compLeft (diagonalComplex k B ej hej D)
  have heq : diagonalComplex k B ej hej D ≫ F.map (w ≫ p ≫ inc) =
      iota p q h ei hei D t ≫ arrowComplex k B ei ej a hja
        (LittleFinitistic.RectificationTotal.total p q h) -
        f ≫ iota p q h ej hej E u := by
    rw [← Category.assoc w p inc, hw, Preadditive.sub_comp, Functor.map_sub,
      Preadditive.comp_sub]
    apply congrArg₂ (fun x y => x - y)
    · change diagonalComplex k B ej hej D ≫
          (vertexComplex k B ej).map ((path k B ei ej a hai D ≫ t) ≫ inc) = _
      rw [Category.assoc, Functor.map_comp, ← Category.assoc,
        diagonal_path k B ei ej a hei hej hai hja D, Category.assoc,
        ← arrow_naturality]
      rfl
    · change diagonalComplex k B ej hej D ≫
          (vertexComplex k B ej).map (((columnComplex k B ej).map f ≫ u) ≫ inc) = _
      rw [Category.assoc, Functor.map_comp, ← Category.assoc, ← diagonal_naturality]
      rfl
  refine Homotopy.equivSubZero.symm ?_
  change Homotopy (diagonalComplex k B ej hej D ≫ F.map (w ≫ p ≫ inc))
    (diagonalComplex k B ej hej D ≫ F.map (w ≫ 0)) at hh
  rw [comp_zero, Functor.map_zero, comp_zero, heq] at hh
  exact hh

variable {A J R : Type} [Fintype A] [Fintype J] [Fintype R]
variable (s : Quadratic k B (A := A) (J := J) (R := R))
variable (D₀ D₁ D₂ : RightComplex B)
variable (f : A → (D₀ ⟶ D₁)) (g : J → (D₁ ⟶ D₂))
variable (H : ∀ r, Homotopy (relationMap s D₀ D₁ D₂ f g r) 0)

abbrev actualP : BiComplex k B := LittleFinitistic.RectificationTotal.total
  (p s D₀ D₁ D₂ f g) (q s D₀ D₁ D₂ f g) (nullHomotopy s D₀ D₁ D₂ f g H)

abbrev iota0 (he : s.e₀ * s.e₀ = s.e₀) :=
  iota (p s D₀ D₁ D₂ f g) (q s D₀ D₁ D₂ f g) (nullHomotopy s D₀ D₁ D₂ f g H)
    s.e₀ he D₀ (inducedData s D₀ D₁ D₂ f g).in₀
abbrev iota1 (he : s.e₁ * s.e₁ = s.e₁) :=
  iota (p s D₀ D₁ D₂ f g) (q s D₀ D₁ D₂ f g) (nullHomotopy s D₀ D₁ D₂ f g H)
    s.e₁ he D₁ (inducedData s D₀ D₁ D₂ f g).in₁
abbrev iota2 (he : s.e₂ * s.e₂ = s.e₂) :=
  iota (p s D₀ D₁ D₂ f g) (q s D₀ D₁ D₂ f g) (nullHomotopy s D₀ D₁ D₂ f g H)
    s.e₂ he D₂ (inducedData s D₀ D₁ D₂ f g).in₂

/-- Compatibility of the actual original vertex-zero insertion with every 0-to-1 arrow. -/
def compatibility01 (h₀ : s.e₀ * s.e₀ = s.e₀) (h₁ : s.e₁ * s.e₁ = s.e₁)
    (a : A) (ha : s.e₁ * s.a a = s.a a) :
    Homotopy (iota0 s D₀ D₁ D₂ f g H h₀ ≫
      arrowComplex k B s.e₀ s.e₁ (s.a a) ha (actualP s D₀ D₁ D₂ f g H))
      (f a ≫ iota1 s D₀ D₁ D₂ f g H h₁) :=
  compatibility _ _ _ _ _ _ h₀ h₁ (s.ha a) ha (f a) _ _
    (biproduct.ι (inducedData s D₀ D₁ D₂ f g).U a ≫ biprod.inl)
    (p_arrow01 s D₀ D₁ D₂ f g a)

/-- Compatibility of the actual original vertex-one insertion with every 1-to-2 arrow. -/
def compatibility12 (h₁ : s.e₁ * s.e₁ = s.e₁) (h₂ : s.e₂ * s.e₂ = s.e₂)
    (b : J) (hb : s.e₂ * s.b b = s.b b) :
    Homotopy (iota1 s D₀ D₁ D₂ f g H h₁ ≫
      arrowComplex k B s.e₁ s.e₂ (s.b b) hb (actualP s D₀ D₁ D₂ f g H))
      (g b ≫ iota2 s D₀ D₁ D₂ f g H h₂) :=
  compatibility _ _ _ _ _ _ h₁ h₂ (s.hb b) hb (g b) _ _
    (biproduct.ι (inducedData s D₀ D₁ D₂ f g).V b ≫ biprod.inr)
    (p_arrow12 s D₀ D₁ D₂ f g b)
end ExternalTensor.Section4.ArrowVertex

end

end OAI
