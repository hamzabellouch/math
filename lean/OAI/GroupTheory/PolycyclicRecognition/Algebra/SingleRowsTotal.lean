import OAI.GroupTheory.PolycyclicRecognition.Finiteness.BicomplexZeroRows

namespace OAI

/-! # Totalization of a bicomplex supported in row zero -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory HomologicalComplex
open Finset.HasAntidiagonal
attribute [local instance 2000] ModuleCat.isModule
attribute [local instance 2300] Pi.module

abbrev singleRowsBicomplex (C : ChainComplex (ModuleCat.{0} ℤ) ℕ) : NatBicomplex :=
  ((ChainComplex.single₀ (ModuleCat ℤ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj C

abbrev diagonalZeroIndex (n : ℕ) : ↥(antidiagonal n) :=
  ⟨(n, 0), mem_antidiagonal.mpr (Nat.add_zero n)⟩

def singleRowsTotalTo (C : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ) :
    ((singleRowsBicomplex C).total (ComplexShape.down ℕ)).X n →ₗ[ℤ] C.X n :=
  (LinearMap.proj (diagonalZeroIndex n)).comp (bicomplexToDiagonal (singleRowsBicomplex C) n)

def singleRowsTotalFrom (C : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ) :
    C.X n →ₗ[ℤ] ((singleRowsBicomplex C).total (ComplexShape.down ℕ)).X n :=
  ((singleRowsBicomplex C).ιTotal (ComplexShape.down ℕ) n 0 n (Nat.add_zero n)).hom

theorem singleRowsTotal_to_from (C : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ) (x : C.X n) :
    singleRowsTotalTo C n (singleRowsTotalFrom C n x) = x := by
  change bicomplexToDiagonal (singleRowsBicomplex C) n
    (((singleRowsBicomplex C).ιTotal _ n 0 n (Nat.add_zero n)).hom x) (diagonalZeroIndex n) = x
  erw [bicomplexToDiagonal_ι (singleRowsBicomplex C) n (diagonalZeroIndex n),
    Pi.single_eq_same]

theorem singleRowsTotal_from_to (C : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ)
    (x : ((singleRowsBicomplex C).total (ComplexShape.down ℕ)).X n) :
    singleRowsTotalFrom C n (singleRowsTotalTo C n x) = x := by
  classical
  apply (bicomplexDiagonalEquiv (singleRowsBicomplex C) n).injective
  change bicomplexToDiagonal (singleRowsBicomplex C) n
    (((singleRowsBicomplex C).ιTotal _ n 0 n (Nat.add_zero n)).hom (singleRowsTotalTo C n x)) = _
  erw [bicomplexToDiagonal_ι (singleRowsBicomplex C) n (diagonalZeroIndex n)]
  ext q
  by_cases hq : q = diagonalZeroIndex n
  · subst q
    erw [Pi.single_eq_same]
    rfl
  · have hj : q.1.2 ≠ 0 := by
      intro hj
      apply hq
      apply Subtype.ext
      have hn := mem_antidiagonal.mp q.2
      apply Prod.ext <;> dsimp [diagonalZeroIndex] at * <;> omega
    have : Subsingleton (((singleRowsBicomplex C).X q.1.1).X q.1.2) :=
      ModuleCat.subsingleton_of_isZero
        (isZero_single_obj_X (ComplexShape.down ℕ) 0 (C.X q.1.1) q.1.2 hj)
    exact Subsingleton.elim _ _

def singleRowsTotalEquiv (C : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ) :
    ((singleRowsBicomplex C).total (ComplexShape.down ℕ)).X n ≃ₗ[ℤ] C.X n :=
  LinearEquiv.ofLinearMap (singleRowsTotalTo C n) (singleRowsTotalFrom C n)
    (LinearMap.ext (singleRowsTotal_to_from C n))
    (LinearMap.ext (singleRowsTotal_from_to C n))

theorem singleRowsTotal_d (C : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ)
    (x : ((singleRowsBicomplex C).total (ComplexShape.down ℕ)).X (n + 1)) :
    (C.d (n + 1) n).hom (singleRowsTotalTo C (n + 1) x) =
      singleRowsTotalTo C n
        ((((singleRowsBicomplex C).total (ComplexShape.down ℕ)).d (n + 1) n).hom x) := by
  have h := bicomplexDiagonalDifferential_apply (singleRowsBicomplex C) n
    (diagonalZeroIndex n) (bicomplexToDiagonal (singleRowsBicomplex C) (n + 1) x)
  simp only [bicomplexDiagonalDifferential, LinearMap.comp_apply,
    bicomplexFromToDiagonal] at h
  have hd : (((singleRowsBicomplex C).d (n + 1) n).f 0) = C.d (n + 1) n :=
    ChainComplex.single₀_map_f_zero _
  have hv : (((singleRowsBicomplex C).X n).d 1 0) = 0 := rfl
  change _ = (((singleRowsBicomplex C).d (n + 1) n).f 0).hom _ +
    (-1 : ℤˣ) ^ n • (((singleRowsBicomplex C).X n).d 1 0).hom _ at h
  rw [hd] at h
  simp only [hv, ModuleCat.hom_zero, LinearMap.zero_apply, Units.smul_def, zsmul_zero,
    add_zero] at h
  exact h.symm

def singleRowsTotalIso (C : ChainComplex (ModuleCat.{0} ℤ) ℕ) :
    (singleRowsBicomplex C).total (ComplexShape.down ℕ) ≅ C :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (singleRowsTotalEquiv C n).toModuleIso) (by
    intro i j hij
    obtain rfl : i = j + 1 := hij.symm
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact singleRowsTotal_d C j x)

end PolycyclicRecognition

end

end OAI
