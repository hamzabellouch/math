import OAI.GroupTheory.PolycyclicRecognition.Finiteness.BicomplexFilteredHomology

namespace OAI

/-! # A horizontal boundary represented by a row cycle

The vertical part of the total differential vanishes on a row cycle. Thus
its total boundary has exactly the single horizontal component used by the
second-page filtration argument.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory HomologicalComplex
open Finset.HasAntidiagonal
attribute [local instance 2000] ModuleCat.isModule
attribute [local instance 2300] Pi.module Submodule.module
variable {R : Type} [CommRing R] (K : NatBicomplex R)

theorem diagonalBoundary_horizontal_cycle (n p j : ℕ) (h : p + j = n)
    (w : (K.X (p + 1)).X j) (hw : ((K.X (p + 1)).d j (j - 1)).hom w = 0) :
    bicomplexDiagonalDifferential K n
        (Pi.single (diagonalSucc₁ ⟨(p, j), mem_antidiagonal.mpr h⟩) w) =
      Pi.single ⟨(p, j), mem_antidiagonal.mpr h⟩ (((K.d (p + 1) p).f j).hom w) := by
  rw [bicomplexDiagonalDifferential_single]
  change bicomplexToDiagonal K n ((K.d₁ (ComplexShape.down ℕ) (p + 1) j n).hom w) +
      bicomplexToDiagonal K n ((K.d₂ (ComplexShape.down ℕ) (p + 1) j n).hom w) = _
  rw [bicomplexToDiagonal_d₁_succ K n p j h]
  have hz : bicomplexToDiagonal K n
      ((K.d₂ (ComplexShape.down ℕ) (p + 1) j n).hom w) = 0 := by
    cases j with
    | zero => exact bicomplexToDiagonal_d₂_zero K n (p + 1) w
    | succ j =>
      rw [bicomplexToDiagonal_d₂_succ K n (p + 1) j (by omega)]
      have hidx : j + 1 - 1 = j := by omega
      rw [hidx] at hw
      rw [hw, Pi.single_zero]
      simp only [Units.smul_def, zsmul_zero]
  rw [hz, add_zero]

def diagonalBoundaryCycle (n : ℕ) (u : bicomplexDiagonal K (n + 1)) :
    (K.total (ComplexShape.down ℕ)).cycles n :=
  (K.total (ComplexShape.down ℕ)).toCycles (n + 1) n
    (bicomplexFromDiagonal K (n + 1) u)

theorem diagonalBoundaryCycle_coordinates (n : ℕ) (u : bicomplexDiagonal K (n + 1)) :
    bicomplexToDiagonal K n ((K.total (ComplexShape.down ℕ)).iCycles n
      (diagonalBoundaryCycle K n u)) = bicomplexDiagonalDifferential K n u := by
  have he := congrArg (fun f => f (bicomplexFromDiagonal K (n + 1) u))
    ((K.total (ComplexShape.down ℕ)).toCycles_i (n + 1) n)
  change (K.total (ComplexShape.down ℕ)).iCycles n (diagonalBoundaryCycle K n u) = _ at he
  rw [he]
  rfl

theorem diagonalBoundaryCycle_homology (n : ℕ) (u : bicomplexDiagonal K (n + 1)) :
    (K.total (ComplexShape.down ℕ)).homologyπ n (diagonalBoundaryCycle K n u) = 0 :=
  congrArg (fun f => f (bicomplexFromDiagonal K (n + 1) u))
    ((K.total (ComplexShape.down ℕ)).toCycles_comp_homologyπ (n + 1) n)

def horizontalBoundaryCycle (n p j : ℕ) (h : p + j = n)
    (w : (K.X (p + 1)).cycles j) : boundedTotalCycles K n (p + 1) := by
  let q : ↥(antidiagonal n) := ⟨(p, j), mem_antidiagonal.mpr h⟩
  refine ⟨diagonalBoundaryCycle K n
    (Pi.single (diagonalSucc₁ q) (((K.X (p + 1)).iCycles j).hom w)), ?_⟩
  apply (mem_boundedTotalCycles K n (p + 1) _).mpr
  intro r hr
  rw [diagonalBoundaryCycle_coordinates]
  have hc := diagonalBoundary_horizontal_cycle K n p j h
    (((K.X (p + 1)).iCycles j).hom w)
    (congrArg (fun f => f.hom w) ((K.X (p + 1)).iCycles_d j (j - 1)))
  refine (congrFun hc r).trans ?_
  apply Pi.single_eq_of_ne
  intro he
  have he' := congrArg (fun s : ↥(antidiagonal n) => s.1.1) he
  dsimp at he'
  omega

theorem horizontalBoundaryCycle_leading (n p j : ℕ) (h : p + j = n)
    (w : (K.X (p + 1)).cycles j) :
    boundedTotalLeadingCycles K n p j h (horizontalBoundaryCycle K n p j h w) =
      cyclesMap (K.d (p + 1) p) j w := by
  apply (ModuleCat.mono_iff_injective ((K.X p).iCycles j)).mp inferInstance
  rw [boundedTotalLeadingCycles_apply]
  change bicomplexToDiagonal K n ((K.total (ComplexShape.down ℕ)).iCycles n
    (diagonalBoundaryCycle K n _)) _ = _
  rw [diagonalBoundaryCycle_coordinates]
  have hc := congrFun (diagonalBoundary_horizontal_cycle K n p j h
    (((K.X (p + 1)).iCycles j).hom w)
    (congrArg (fun f => f.hom w) ((K.X (p + 1)).iCycles_d j (j - 1))))
      ⟨(p, j), mem_antidiagonal.mpr h⟩
  rw [Pi.single_eq_same] at hc
  exact hc.trans (congrArg (fun f => f w) (cyclesMap_i (K.d (p + 1) p) j)).symm

theorem horizontalBoundaryCycle_leading_homology (n p j : ℕ) (h : p + j = n)
    (w : (K.X (p + 1)).cycles j) :
    boundedTotalLeadingHomology K n p j h (horizontalBoundaryCycle K n p j h w) =
      homologyMap (K.d (p + 1) p) j ((K.X (p + 1)).homologyπ j w) := by
  change (K.X p).homologyπ j (boundedTotalLeadingCycles K n p j h _) = _
  rw [horizontalBoundaryCycle_leading]
  exact (congrArg (fun f => f w) (homologyπ_naturality (K.d (p + 1) p) j)).symm

theorem horizontalBoundaryCycle_homology (n p j : ℕ) (h : p + j = n)
    (w : (K.X (p + 1)).cycles j) :
    (K.total (ComplexShape.down ℕ)).homologyπ n
      (horizontalBoundaryCycle K n p j h w).val = 0 :=
  diagonalBoundaryCycle_homology K n _

end PolycyclicRecognition

end

end OAI
