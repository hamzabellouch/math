import OAI.Algebra.Finitistic.Rectification.ColumnProperties
import Mathlib.Algebra.Category.ModuleCat.Biproducts

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
noncomputable section
namespace ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
attribute [local instance] ExternalTensor.bimodule ExternalTensor.rightModule

def forgetK : ModuleCat.{u} (Enveloping k B) ⥤ ModuleCat.{u} k :=
  ModuleCat.restrictScalars (algebraMap k (Enveloping k B))
instance forgetK_additive : (forgetK k B).Additive := by
  dsimp [forgetK]
  infer_instance

def columnKIso (e : B) (N : ModuleCat.{u} Bᵐᵒᵖ) :
    (forgetK k B).obj ((columnFunctor k B e).obj N) ≅
      ModuleCat.of k (Column k B N e) :=
  (show ((forgetK k B).obj ((columnFunctor k B e).obj N)) ≃ₗ[k]
      (ModuleCat.of k (Column k B N e)) from
    { toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun c x => by
        change (algebraMap k (Enveloping k B) c) •
          (show Column k B N e from x) = c • (show Column k B N e from x)
        exact IsScalarTower.algebraMap_smul (Enveloping k B) c (show Column k B N e from x) }).toModuleIso

theorem finite_of_iso {X Y : ModuleCat.{u} k} (e : X ≅ Y)
    (hY : FiniteDimensional k Y) : FiniteDimensional k X := by
  let := hY
  exact FiniteDimensional.of_injective e.hom.hom e.toLinearEquiv.injective

theorem column_finite [FiniteDimensional k B] (e : B)
    (N : ModuleCat.{u} Bᵐᵒᵖ) [Module.Finite Bᵐᵒᵖ N] :
    FiniteDimensional k ((forgetK k B).obj ((columnFunctor k B e).obj N)) :=
  finite_of_iso k (columnKIso k B e N) (column_finiteDimensional k B N e)

abbrev termK (n : ℤ) : BiComplex k B ⥤ ModuleCat.{u} k :=
  eval _ _ n ⋙ forgetK k B

theorem sum_finite {I : Type} [Fintype I] (K : I → BiComplex k B)
    (n : ℤ) (hK : ∀ i, FiniteDimensional k ((termK k B n).obj (K i))) :
    FiniteDimensional k ((termK k B n).obj (⨁ K)) := by
  let (i : I) : FiniteDimensional k ((termK k B n).obj (K i)) := hK i
  apply finite_of_iso k ((termK k B n).mapBiproduct K ≪≫ ModuleCat.biproductIsoPi _)
  change Module.Finite k (∀ i, ((termK k B n).obj (K i)))
  infer_instance

theorem biprod_finite {X Y : ModuleCat.{u} k}
    (hX : FiniteDimensional k X) (hY : FiniteDimensional k Y) :
    FiniteDimensional k (X ⊞ Y : ModuleCat.{u} k) := by
  let := hX
  let := hY
  apply finite_of_iso k (ModuleCat.biprodIsoProd X Y)
  change Module.Finite k (X × Y)
  infer_instance

theorem biprod_term_finite (K L : BiComplex k B) (n : ℤ)
    (hK : FiniteDimensional k ((termK k B n).obj K))
    (hL : FiniteDimensional k ((termK k B n).obj L)) :
    FiniteDimensional k ((termK k B n).obj (K ⊞ L)) := by
  let := preservesBinaryBiproducts_of_preservesBiproducts (termK k B n)
  exact finite_of_iso k ((termK k B n).mapBiprod K L) (biprod_finite k hK hL)

variable {k B}
variable {A J R : Type} [Fintype A] [Fintype J] [Fintype R]
variable (s : Quadratic k B (A := A) (J := J) (R := R))
variable (D₀ D₁ D₂ : RightComplex B)
variable (f : A → (D₀ ⟶ D₁)) (g : J → (D₁ ⟶ D₂))

/-- Finite-dimensionality of the actual three induced columns, from exactly
finite-dimensional B and finite generation of the right-module input terms. -/
theorem columns_finite [FiniteDimensional k B]
    (h₀ : ∀ n, Module.Finite Bᵐᵒᵖ (D₀.X n))
    (h₁ : ∀ n, Module.Finite Bᵐᵒᵖ (D₁.X n))
    (h₂ : ∀ n, Module.Finite Bᵐᵒᵖ (D₂.X n)) (n : ℤ) :
    FiniteDimensional k ((forgetK k B).obj ((L0Prime s D₀ D₁ D₂ f g).X n)) ∧
    FiniteDimensional k ((forgetK k B).obj ((L1Prime s D₀ D₁ D₂ f g).X n)) ∧
    FiniteDimensional k ((forgetK k B).obj ((L2Prime s D₀ D₁ D₂ f g).X n)) := by
  let := h₀ n
  let := h₁ n
  let := h₂ n
  refine ⟨?_, ?_, ?_⟩
  · apply biprod_term_finite
    · exact column_finite k B s.e₀ (D₀.X n)
    · apply biprod_term_finite
      · exact column_finite k B s.e₁ (D₁.X n)
      · exact column_finite k B s.e₂ (D₂.X n)
  · apply biprod_term_finite
    · apply sum_finite
      intro a
      exact column_finite k B s.e₁ (D₀.X n)
    · apply sum_finite
      intro b
      exact column_finite k B s.e₂ (D₁.X n)
  · apply sum_finite
    intro r
    exact column_finite k B s.e₂ (D₀.X n)
end ExternalTensor.Section4

end

end OAI
