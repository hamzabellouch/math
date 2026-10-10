import OAI.Algebra.Finitistic.Bimodule.BimoduleVertex
import OAI.Algebra.Finitistic.Rectification.InducedRectification
import OAI.Algebra.Finitistic.Rectification.ArrowCompatibility

namespace OAI
open CategoryTheory HomologicalComplex
open scoped TensorProduct
noncomputable section
namespace ExternalTensor.Section4.ArrowVertex.NativeBridge
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]

/-- The native and generic functors retain definitionally the same original fixed submodule. -/
theorem vertex_eq (e : B) : vertex k B e = LittleFinitistic.BimoduleVertex.functor k B e := rfl

variable {k B}
variable {A J R : Type} [Fintype A] [Fintype J] [Fintype R]
variable (s : Quadratic k B (A := A) (J := J) (R := R))
variable (D₀ D₁ D₂ : RightComplex B)
variable (f : A → (D₀ ⟶ D₁)) (g : J → (D₁ ⟶ D₂))
variable (H : ∀ r, Homotopy (relationMap s D₀ D₁ D₂ f g r) 0)

/-- The native P is exactly the total already used for actual arrow compatibility. -/
theorem total_eq : actualP s D₀ D₁ D₂ f g H =
    LittleFinitistic.InducedRectification.total s D₀ D₁ D₂ f g H := rfl

/-- The native zero-column inclusion is exactly the one in the proved endpoints. -/
theorem inclusion_eq : LittleFinitistic.RectificationTotal.inclusion
    (p s D₀ D₁ D₂ f g) (q s D₀ D₁ D₂ f g) (nullHomotopy s D₀ D₁ D₂ f g H) =
      LittleFinitistic.InducedRectification.inclusion s D₀ D₁ D₂ f g H := rfl

abbrev nativeVertex (e : B) :=
  (LittleFinitistic.BimoduleVertex.functor k B e).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The direct original insertion in the native P and native fixed-submodule functor. -/
def originalIota (e : B) (he : e * e = e) (D : RightComplex B)
    (t : (columnComplex k B e).obj D ⟶ L0Prime s D₀ D₁ D₂ f g) :
    D ⟶ (nativeVertex e).obj (LittleFinitistic.InducedRectification.total s D₀ D₁ D₂ f g H) :=
  diagonalComplex k B e he D ≫ (nativeVertex e).map t ≫
    (nativeVertex e).map (LittleFinitistic.InducedRectification.inclusion s D₀ D₁ D₂ f g H)

/-- No comparison hypothesis is needed to identify the proved insertion with native maps. -/
theorem iota_eq_original (e : B) (he : e * e = e) (D : RightComplex B)
    (t : (columnComplex k B e).obj D ⟶ L0Prime s D₀ D₁ D₂ f g) :
    iota (p s D₀ D₁ D₂ f g) (q s D₀ D₁ D₂ f g)
      (nullHomotopy s D₀ D₁ D₂ f g H) e he D t =
      originalIota s D₀ D₁ D₂ f g H e he D t := by
  simp only [iota, originalIota, Functor.map_comp]
  rfl

/-- The native original diagonal map is determined by its tensor formula. -/
theorem diagonal_eq_of_original (e : B) (he : e * e = e) (D : RightComplex B)
    (j : D ⟶ (nativeVertex e).obj ((columnComplex k B e).obj D))
    (hj : ∀ n x, ((j.f n) x).val = generator B e ⊗ₜ[k] x) :
    j = diagonalComplex k B e he D := by
  ext n x
  apply Subtype.ext
  exact hj n x

/-- Actual arrow-01 compatibility with the native P, vertex functors and inclusions. -/
def nativeCompatibility01 (h₀ : s.e₀ * s.e₀ = s.e₀) (h₁ : s.e₁ * s.e₁ = s.e₁)
    (a : A) (ha : s.e₁ * s.a a = s.a a) :
    Homotopy
      (originalIota s D₀ D₁ D₂ f g H s.e₀ h₀ D₀ (inducedData s D₀ D₁ D₂ f g).in₀ ≫
        arrowComplex k B s.e₀ s.e₁ (s.a a) ha
          (LittleFinitistic.InducedRectification.total s D₀ D₁ D₂ f g H))
      (f a ≫ originalIota s D₀ D₁ D₂ f g H s.e₁ h₁ D₁
        (inducedData s D₀ D₁ D₂ f g).in₁) := by
  have ht := compatibility01 s D₀ D₁ D₂ f g H h₀ h₁ a ha
  dsimp only [iota0, iota1] at ht
  erw [iota_eq_original s D₀ D₁ D₂ f g H,
    iota_eq_original s D₀ D₁ D₂ f g H] at ht
  exact ht

/-- Actual arrow-12 compatibility with the native P, vertex functors and inclusions. -/
def nativeCompatibility12 (h₁ : s.e₁ * s.e₁ = s.e₁) (h₂ : s.e₂ * s.e₂ = s.e₂)
    (b : J) (hb : s.e₂ * s.b b = s.b b) :
    Homotopy
      (originalIota s D₀ D₁ D₂ f g H s.e₁ h₁ D₁ (inducedData s D₀ D₁ D₂ f g).in₁ ≫
        arrowComplex k B s.e₁ s.e₂ (s.b b) hb
          (LittleFinitistic.InducedRectification.total s D₀ D₁ D₂ f g H))
      (g b ≫ originalIota s D₀ D₁ D₂ f g H s.e₂ h₂ D₂
        (inducedData s D₀ D₁ D₂ f g).in₂) := by
  have ht := compatibility12 s D₀ D₁ D₂ f g H h₁ h₂ b hb
  dsimp only [iota1, iota2] at ht
  erw [iota_eq_original s D₀ D₁ D₂ f g H,
    iota_eq_original s D₀ D₁ D₂ f g H] at ht
  exact ht
end ExternalTensor.Section4.ArrowVertex.NativeBridge

end

end OAI
