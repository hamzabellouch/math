import Mathlib.LinearAlgebra.Basis.Defs
import OAI.Computability.PerfectCompleteness.Algebra.UniformLinearImage
import OAI.Computability.PerfectCompleteness.Sampling.RationalFiniteLawLemmas
import OAI.Computability.UniqueGames.Analysis.MatrixRestrictions
import OAI.Computability.UniqueGames.Foundations.SamplingLemmas

namespace OAI


namespace PerfectCompleteness.RestrictionRowsLaw

noncomputable section

open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Fourier.MatrixRestrictions
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

variable {E C I : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup C] [Module F2 C] [Fintype I]
  (W : Submodule F2 E) (C' : Submodule F2 C) (b : Module.Basis I F2 C')

def rowsLinear : Parameter W C' →ₗ[F2] (I → Module.Dual F2 (E ⧸ W)) where
  toFun A i := (b.coord i).comp A
  map_add' A B := by
    funext i
    apply LinearMap.ext
    intro x
    exact map_add (b.coord i) (A x) (B x)
  map_smul' a A := by
    funext i
    apply LinearMap.ext
    intro x
    exact map_smul (b.coord i) a (A x)

omit [Fintype I] in
@[simp] theorem rowsLinear_apply (A : Parameter W C') (i : I) :
    rowsLinear W C' b A i = (b.coord i).comp A := rfl

def fromRows (rows : I → Module.Dual F2 (E ⧸ W)) : Parameter W C' :=
  b.equivFun.symm.toLinearMap.comp (LinearMap.pi rows)

@[simp] theorem rowsLinear_fromRows (rows : I → Module.Dual F2 (E ⧸ W)) :
    rowsLinear W C' b (fromRows W C' b rows) = rows := by
  funext i
  apply LinearMap.ext
  intro x
  exact b.coord_equivFun_symm i (fun j => rows j x)

theorem rowsLinear_surjective : Function.Surjective (rowsLinear W C' b) :=
  fun rows => ⟨fromRows W C' b rows, rowsLinear_fromRows W C' b rows⟩

omit [Fintype I] in
theorem rowsLinear_injective : Function.Injective (rowsLinear W C' b) := by
  intro A B h
  apply LinearMap.ext
  intro x
  apply b.repr.injective
  ext i
  exact congrArg (fun rows : I → Module.Dual F2 (E ⧸ W) => rows i x) h

def rowsEquiv : Parameter W C' ≃ₗ[F2] (I → Module.Dual F2 (E ⧸ W)) :=
  LinearEquiv.ofBijective (rowsLinear W C' b)
    ⟨rowsLinear_injective W C' b, rowsLinear_surjective W C' b⟩

section Selection

variable {J : Type*} (sel : J → I)

def selectLinear : (I → Module.Dual F2 (E ⧸ W)) →ₗ[F2]
    (J → Module.Dual F2 (E ⧸ W)) :=
  LinearMap.pi (fun j => LinearMap.proj (sel j))

omit [Fintype I] in
theorem selectLinear_surjective (hsel : Function.Injective sel) :
    Function.Surjective (selectLinear W sel) :=
  hsel.surjective_comp_right

def selectedRowsLinear : Parameter W C' →ₗ[F2] (J → Module.Dual F2 (E ⧸ W)) :=
  (selectLinear W sel).comp (rowsLinear W C' b)

omit [Fintype I] in
@[simp] theorem selectedRowsLinear_apply (A : Parameter W C') (j : J) :
    selectedRowsLinear W C' b sel A j = (b.coord (sel j)).comp A := rfl

theorem selectedRowsLinear_surjective (hsel : Function.Injective sel) :
    Function.Surjective (selectedRowsLinear W C' b sel) :=
  (selectLinear_surjective W sel hsel).comp (rowsLinear_surjective W C' b)

end Selection

section Uniform

variable [Fintype (Parameter W C')] [Fintype (Module.Dual F2 (E ⧸ W))]

theorem uniform_rowsLinear :
    (FiniteDistribution.uniform (Parameter W C')).pushforward (rowsLinear W C' b) =
      FiniteDistribution.uniform (I → Module.Dual F2 (E ⧸ W)) :=
  UniformLinearImage.uniform_pushforward_linearMap
    (rowsLinear W C' b) (rowsLinear_surjective W C' b)

theorem uniform_rows_law [DecidableEq I] :
    (FiniteDistribution.uniform (Parameter W C')).pushforward (rowsLinear W C' b) =
      FiniteProduct.law (fun _ : I => FiniteDistribution.uniform
        (Module.Dual F2 (E ⧸ W))) := by
  rw [UniformLinearImage.law_uniform]
  exact UniformLinearImage.uniform_pushforward_linearMap
    (rowsLinear W C' b) (rowsLinear_surjective W C' b)

private theorem uniform_add_left {V : Type*} [AddGroup V] [Fintype V] (offset : V) :
    (FiniteDistribution.uniform V).pushforward (fun x => offset + x) =
      FiniteDistribution.uniform V := by
  change (FiniteDistribution.uniform V).pushforward (Equiv.addLeft offset) = _
  rw [FiniteDistribution.pushforward_equiv]
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  rfl

theorem uniform_translated_rows (offsets : I → Module.Dual F2 (E ⧸ W)) :
    (FiniteDistribution.uniform (Parameter W C')).pushforward
        (fun A => offsets + rowsLinear W C' b A) =
      FiniteDistribution.uniform (I → Module.Dual F2 (E ⧸ W)) := by
  rw [← FiniteDistribution.pushforward_comp
    (FiniteDistribution.uniform (Parameter W C')) (rowsLinear W C' b)
    (fun rows => offsets + rows), uniform_rowsLinear]
  exact uniform_add_left offsets

variable {J : Type*} [Fintype J] (sel : J → I)

theorem uniform_selectedRowsLinear (hsel : Function.Injective sel) :
    (FiniteDistribution.uniform (Parameter W C')).pushforward
        (selectedRowsLinear W C' b sel) =
      FiniteDistribution.uniform (J → Module.Dual F2 (E ⧸ W)) :=
  UniformLinearImage.uniform_pushforward_linearMap
    (selectedRowsLinear W C' b sel) (selectedRowsLinear_surjective W C' b sel hsel)

theorem uniform_selected_rows_law [DecidableEq J] (hsel : Function.Injective sel) :
    (FiniteDistribution.uniform (Parameter W C')).pushforward
        (selectedRowsLinear W C' b sel) =
      FiniteProduct.law (fun _ : J => FiniteDistribution.uniform
        (Module.Dual F2 (E ⧸ W))) := by
  rw [UniformLinearImage.law_uniform]
  exact UniformLinearImage.uniform_pushforward_linearMap
    (selectedRowsLinear W C' b sel) (selectedRowsLinear_surjective W C' b sel hsel)

end Uniform

def affineRow (offset : Module.Dual F2 E) (row : Module.Dual F2 (E ⧸ W)) :
    Module.Dual F2 E := offset + row.comp W.mkQ

omit [Fintype I] in
theorem coordinate_translate (coordinates : I → Module.Dual F2 C)
    (hcoordinates : ∀ i, (coordinates i).comp C'.subtype = b.coord i)
    (X : E →ₗ[F2] C) (A : Parameter W C') (i : I) :
    (coordinates i).comp (translate W C' X A) =
      affineRow W ((coordinates i).comp X) (rowsLinear W C' b A i) := by
  apply LinearMap.ext
  intro x
  change coordinates i (X x + (A (W.mkQ x) : C)) =
    coordinates i (X x) + b.coord i (A (W.mkQ x))
  rw [map_add]
  congr 1
  exact congrArg (fun f : C' →ₗ[F2] F2 => f (A (W.mkQ x))) (hcoordinates i)


variable [Fintype (Parameter W C')] [Fintype (Module.Dual F2 (E ⧸ W))]
  [Fintype (Module.Dual F2 E)]

def affineRowLaw (offset : Module.Dual F2 E) : FiniteDistribution (Module.Dual F2 E) :=
  (FiniteDistribution.uniform (Module.Dual F2 (E ⧸ W))).pushforward (affineRow W offset)

theorem uniform_affine_rows_law [DecidableEq I] (offsets : I → Module.Dual F2 E) :
    (FiniteDistribution.uniform (Parameter W C')).pushforward
        (fun A i => affineRow W (offsets i) (rowsLinear W C' b A i)) =
      FiniteProduct.law (fun i => affineRowLaw W (offsets i)) := by
  rw [← FiniteDistribution.pushforward_comp
    (FiniteDistribution.uniform (Parameter W C')) (rowsLinear W C' b)
    (fun rows i => affineRow W (offsets i) (rows i)), uniform_rows_law]
  exact FiniteProduct.pushforward_map _ (fun i => affineRow W (offsets i))

theorem uniform_coordinate_translate_law [DecidableEq I]
    (coordinates : I → Module.Dual F2 C)
    (hcoordinates : ∀ i, (coordinates i).comp C'.subtype = b.coord i)
    (X : E →ₗ[F2] C) :
    (FiniteDistribution.uniform (Parameter W C')).pushforward
        (fun A i => (coordinates i).comp (translate W C' X A)) =
      FiniteProduct.law (fun i => affineRowLaw W ((coordinates i).comp X)) := by
  have hrows : (fun A i => (coordinates i).comp (translate W C' X A)) =
      (fun A i => affineRow W ((coordinates i).comp X) (rowsLinear W C' b A i)) := by
    funext A i
    exact coordinate_translate W C' b coordinates hcoordinates X A i
  rw [hrows]
  exact uniform_affine_rows_law W C' b (fun i => (coordinates i).comp X)

variable {J : Type*} [Fintype J] [DecidableEq J]

theorem uniform_selected_affine_rows_law (sel : J → I)
    (hsel : Function.Injective sel) (offsets : J → Module.Dual F2 E) :
    (FiniteDistribution.uniform (Parameter W C')).pushforward
        (fun A j => affineRow W (offsets j) (selectedRowsLinear W C' b sel A j)) =
      FiniteProduct.law (fun j => affineRowLaw W (offsets j)) := by
  rw [← FiniteDistribution.pushforward_comp
    (FiniteDistribution.uniform (Parameter W C')) (selectedRowsLinear W C' b sel)
    (fun rows j => affineRow W (offsets j) (rows j)),
    uniform_selected_rows_law W C' b sel hsel]
  exact FiniteProduct.pushforward_map _ (fun j => affineRow W (offsets j))

end
end PerfectCompleteness.RestrictionRowsLaw

end OAI
