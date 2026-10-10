import OAI.Algebra.Finitistic.Rectification.InducedDiagram
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Homology.HomologicalComplexBiprod

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
noncomputable section
namespace ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
attribute [local instance] ExternalTensor.bimodule ExternalTensor.rightModule

/-- Restrict genuine bimodules to right B-modules. -/
def forgetRight : ModuleCat.{u} (Enveloping k B) ⥤ ModuleCat.{u} Bᵐᵒᵖ :=
  ModuleCat.restrictScalars (Algebra.TensorProduct.includeRight :
    Bᵐᵒᵖ →ₐ[k] Enveloping k B).toRingHom

instance forgetRight_additive : (forgetRight k B).Additive := by
  dsimp [forgetRight]
  infer_instance

/-- The restricted action is the right action already verified for the actual tensor. -/
def columnRightIso (e : B) (N : ModuleCat.{u} Bᵐᵒᵖ) :
    (forgetRight k B).obj ((columnFunctor k B e).obj N) ≅
      ModuleCat.of Bᵐᵒᵖ (Column k B N e) :=
  (show ((forgetRight k B).obj ((columnFunctor k B e).obj N)) ≃ₗ[Bᵐᵒᵖ]
      (ModuleCat.of Bᵐᵒᵖ (Column k B N e)) from
    { toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun c x => by
        change ((1 ⊗ₜ[k] c : Enveloping k B) • (show Column k B N e from x)) =
          c • (show Column k B N e from x)
        exact (right_eq_enveloping k B (leftIdeal B e) N c x).symm }).toModuleIso

theorem column_right_projective (e : B) (N : ModuleCat.{u} Bᵐᵒᵖ)
    [Module.Projective Bᵐᵒᵖ N] :
    Projective ((forgetRight k B).obj ((columnFunctor k B e).obj N)) := by
  let := column_projective k B N e
  exact Projective.of_iso (columnRightIso k B e N).symm (by infer_instance)

/-- Exact boundedness transfer for each induced column. -/
theorem column_isZero (e : B) (D : RightComplex B) (i : ℤ)
    (hi : IsZero (D.X i)) : IsZero (((columnComplex k B e).obj D).X i) :=
  (columnFunctor k B e).map_isZero hi

instance rightFiniteBiproducts : HasFiniteBiproducts (ModuleCat.{u} Bᵐᵒᵖ) :=
  HasFiniteBiproducts.of_hasFiniteProducts
instance rightBinaryBiproducts : HasBinaryBiproducts (ModuleCat.{u} Bᵐᵒᵖ) :=
  HasBinaryBiproducts.of_hasBinaryProducts

abbrev termRight (n : ℤ) : BiComplex k B ⥤ ModuleCat.{u} Bᵐᵒᵖ :=
  eval _ _ n ⋙ forgetRight k B

theorem sum_right_projective {I : Type} [Fintype I] (K : I → BiComplex k B)
    (n : ℤ) (hK : ∀ i, Projective ((termRight k B n).obj (K i))) :
    Projective ((termRight k B n).obj (⨁ K)) := by
  let (i : I) : Projective ((termRight k B n).obj (K i)) := hK i
  apply Projective.of_iso ((termRight k B n).mapBiproduct K).symm
  refine ⟨fun f e _ => ⟨biproduct.desc (fun i => by
    letI : Projective (((termRight k B n).obj ∘ K) i) := hK i
    exact Projective.factorThru (biproduct.ι ((termRight k B n).obj ∘ K) i ≫ f) e), ?_⟩⟩
  apply biproduct.hom_ext'
  intro i
  let : Projective (((termRight k B n).obj ∘ K) i) := hK i
  simp only [biproduct.ι_desc_assoc, Projective.factorThru_comp]

theorem biprod_right_projective (K L : BiComplex k B) (n : ℤ)
    (hK : Projective ((termRight k B n).obj K))
    (hL : Projective ((termRight k B n).obj L)) :
    Projective ((termRight k B n).obj (K ⊞ L)) := by
  let := hK
  let := hL
  let := preservesBinaryBiproducts_of_preservesBiproducts (termRight k B n)
  exact Projective.of_iso ((termRight k B n).mapBiprod K L).symm (by infer_instance)

theorem sum_isZero {C : Type*} [Category C] [HasZeroMorphisms C]
    {I : Type} (K : I → C) [HasBiproduct K] (hK : ∀ i, IsZero (K i)) :
    IsZero (⨁ K) := by
  apply (IsZero.iff_id_eq_zero _).2
  apply biproduct.hom_ext
  intro i
  simp only [Category.id_comp, zero_comp]
  exact (hK i).eq_zero_of_tgt _

theorem sum_term_isZero {I : Type} [Fintype I] (K : I → BiComplex k B)
    (n : ℤ) (hK : ∀ i, IsZero ((K i).X n)) : IsZero ((⨁ K).X n) := by
  apply ((eval _ _ n).mapBiproduct K).isZero_iff.mpr
  exact sum_isZero _ hK

theorem biprod_term_isZero (K L : BiComplex k B) (n : ℤ)
    (hK : IsZero (K.X n)) (hL : IsZero (L.X n)) : IsZero ((K ⊞ L).X n) := by
  let := preservesBinaryBiproducts_of_preservesBiproducts (eval (ModuleCat (Enveloping k B)) (ComplexShape.up ℤ) n)
  apply ((eval _ _ n).mapBiprod K L).isZero_iff.mpr
  exact (biprod_isZero_iff _ _).mpr ⟨hK, hL⟩

variable {k B}
variable {A J R : Type} [Fintype A] [Fintype J] [Fintype R]
variable (s : Quadratic k B (A := A) (J := J) (R := R))
variable (D₀ D₁ D₂ : RightComplex B)
variable (f : A → (D₀ ⟶ D₁)) (g : J → (D₁ ⟶ D₂))

/-- Exactly the three right-projectivity inputs to RectificationTotal.total_projective_after. -/
theorem columns_right_projective
    (h₀ : ∀ n, Module.Projective Bᵐᵒᵖ (D₀.X n))
    (h₁ : ∀ n, Module.Projective Bᵐᵒᵖ (D₁.X n))
    (h₂ : ∀ n, Module.Projective Bᵐᵒᵖ (D₂.X n)) (n : ℤ) :
    Projective ((forgetRight k B).obj ((L0Prime s D₀ D₁ D₂ f g).X n)) ∧
    Projective ((forgetRight k B).obj ((L1Prime s D₀ D₁ D₂ f g).X n)) ∧
    Projective ((forgetRight k B).obj ((L2Prime s D₀ D₁ D₂ f g).X n)) := by
  let := h₀ n
  let := h₁ n
  let := h₂ n
  refine ⟨?_, ?_, ?_⟩
  · apply biprod_right_projective
    · exact column_right_projective k B s.e₀ (D₀.X n)
    · apply biprod_right_projective
      · exact column_right_projective k B s.e₁ (D₁.X n)
      · exact column_right_projective k B s.e₂ (D₂.X n)
  · apply biprod_right_projective
    · apply sum_right_projective
      intro a
      exact column_right_projective k B s.e₁ (D₀.X n)
    · apply sum_right_projective
      intro b
      exact column_right_projective k B s.e₂ (D₁.X n)
  · apply sum_right_projective
    intro r
    exact column_right_projective k B s.e₂ (D₀.X n)

theorem columns_isZero (n : ℤ) (h₀ : IsZero (D₀.X n))
    (h₁ : IsZero (D₁.X n)) (h₂ : IsZero (D₂.X n)) :
    IsZero ((L0Prime s D₀ D₁ D₂ f g).X n) ∧
    IsZero ((L1Prime s D₀ D₁ D₂ f g).X n) ∧
    IsZero ((L2Prime s D₀ D₁ D₂ f g).X n) := by
  refine ⟨?_, ?_, ?_⟩
  · apply biprod_term_isZero
    · exact column_isZero k B s.e₀ D₀ n h₀
    · apply biprod_term_isZero
      · exact column_isZero k B s.e₁ D₁ n h₁
      · exact column_isZero k B s.e₂ D₂ n h₂
  · apply biprod_term_isZero
    · apply sum_term_isZero
      intro a
      exact column_isZero k B s.e₁ D₀ n h₀
    · apply sum_term_isZero
      intro b
      exact column_isZero k B s.e₂ D₁ n h₁
  · apply sum_term_isZero
    intro r
    exact column_isZero k B s.e₂ D₀ n h₀

/-- Uniform bounds on the input complexes give the same bounds on all three columns. -/
theorem columns_bounded (lo hi : ℤ)
    (h₀ : ∀ n, n < lo ∨ hi < n → IsZero (D₀.X n))
    (h₁ : ∀ n, n < lo ∨ hi < n → IsZero (D₁.X n))
    (h₂ : ∀ n, n < lo ∨ hi < n → IsZero (D₂.X n)) :
    ∀ n, n < lo ∨ hi < n →
      IsZero ((L0Prime s D₀ D₁ D₂ f g).X n) ∧
      IsZero ((L1Prime s D₀ D₁ D₂ f g).X n) ∧
      IsZero ((L2Prime s D₀ D₁ D₂ f g).X n) :=
  fun n hn => columns_isZero s D₀ D₁ D₂ f g n (h₀ n hn) (h₁ n hn) (h₂ n hn)
end ExternalTensor.Section4

end

end OAI
