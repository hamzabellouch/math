import OAI.GroupTheory.PolycyclicRecognition.Finiteness.BicomplexFiniteHomology

namespace OAI

/-! # Leading classes are cycles on the second page

The cycle equation in the adjacent column makes the leading row-homology
class a horizontal cycle. All maps below use actual homology objects.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory HomologicalComplex
open Finset.HasAntidiagonal
attribute [local instance 2000] ModuleCat.isModule
attribute [local instance 2300] Pi.module Submodule.module
variable {R : Type} [CommRing R] (K : NatBicomplex R)

abbrev rowHomologyComplex (j : ℕ) : ChainComplex (ModuleCat R) ℕ :=
  ((homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) j).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj K

theorem boundedTotalLeadingHomology_isCycle (n p j : ℕ) (h : p + j = n)
    (x : boundedTotalCycles K n (p + 1)) :
    (rowHomologyComplex K j).d p (p - 1)
      (boundedTotalLeadingHomology K n p j h x) = 0 := by
  cases p with
  | zero =>
    have hd : (rowHomologyComplex K j).d 0 0 = 0 :=
      (rowHomologyComplex K j).shape 0 0 (by simp [ComplexShape.down])
    rw [hd]
    rfl
  | succ p =>
    let T := K.total (ComplexShape.down ℕ)
    let v := bicomplexToDiagonal K n (T.iCycles n x.val)
    let z := boundedTotalLeadingCycles K n (p + 1) j h x
    let z' := cyclesMap (K.d (p + 1) p) j z
    have hi : (K.X p).iCycles j z' =
        ((K.d (p + 1) p).f j) (v ⟨(p + 1, j), mem_antidiagonal.mpr h⟩) := by
      have he := congrArg (fun f => f z) (cyclesMap_i (K.d (p + 1) p) j)
      change (K.X p).iCycles j z' =
        ((K.d (p + 1) p).f j) ((K.X (p + 1)).iCycles j z) at he
      rw [boundedTotalLeadingCycles_apply] at he
      exact he
    have hv := (totalCycles_isDiagonalCycle K n x.val) p j (by omega)
    let w : (K.X p).X (j + 1) :=
      - ((-1 : ℤˣ) ^ p • v ⟨(p, j + 1), mem_antidiagonal.mpr (by omega)⟩)
    have hw : (K.X p).d (j + 1) j w = (K.X p).iCycles j z' := by
      rw [hi]
      dsimp only [w]
      rw [map_neg]
      have hs : (K.X p).d (j + 1) j
          ((-1 : ℤˣ) ^ p • v ⟨(p, j + 1), mem_antidiagonal.mpr (by omega)⟩) =
          (-1 : ℤˣ) ^ p • (K.X p).d (j + 1) j
            (v ⟨(p, j + 1), mem_antidiagonal.mpr (by omega)⟩) := by
        simp only [Units.smul_def, map_zsmul]
      rw [hs]
      exact (eq_neg_of_add_eq_zero_left hv).symm
    have hz := homologyπ_eq_zero_of_boundary (K.X p) j z' w hw
    have hn := congrArg (fun f => f z) (homologyπ_naturality (K.d (p + 1) p) j)
    exact hn.trans hz

/-- Leading total cycles mapped into the cycles of the first-page complex. -/
def boundedTotalSecondPageCycles (n p j : ℕ) (h : p + j = n) :
    ModuleCat.of R (boundedTotalCycles K n (p + 1)) ⟶
      (rowHomologyComplex K j).cycles p := by
  have hn : (ComplexShape.down ℕ).next p = p - 1 := by
    cases p with
    | zero => exact (ComplexShape.down ℕ).next_eq_self' 0 (by intros; simp [ComplexShape.down])
    | succ p => exact (ComplexShape.down ℕ).next_eq' rfl
  apply (rowHomologyComplex K j).liftCycles
    (ModuleCat.ofHom (boundedTotalLeadingHomology K n p j h)) (p - 1) hn
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact boundedTotalLeadingHomology_isCycle K n p j h x

theorem boundedTotalSecondPageCycles_apply (n p j : ℕ) (h : p + j = n)
    (x : boundedTotalCycles K n (p + 1)) :
    (rowHomologyComplex K j).iCycles p (boundedTotalSecondPageCycles K n p j h x) =
      boundedTotalLeadingHomology K n p j h x := by
  have he : boundedTotalSecondPageCycles K n p j h ≫ (rowHomologyComplex K j).iCycles p =
      ModuleCat.ofHom (boundedTotalLeadingHomology K n p j h) := by
    unfold boundedTotalSecondPageCycles
    exact (rowHomologyComplex K j).liftCycles_i _ _ _ _
  exact congrArg (fun f : ModuleCat.of R (boundedTotalCycles K n (p + 1)) ⟶
    (rowHomologyComplex K j).X p => f.hom x) he

def boundedTotalSecondPageClass (n p j : ℕ) (h : p + j = n) :
    boundedTotalCycles K n (p + 1) →ₗ[R] (rowHomologyComplex K j).homology p :=
  ((rowHomologyComplex K j).homologyπ p).hom.comp
    (boundedTotalSecondPageCycles K n p j h).hom

end PolycyclicRecognition

end

end OAI
