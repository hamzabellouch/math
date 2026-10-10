import OAI.GroupTheory.PolycyclicRecognition.Algebra.RationalModuleFunctor
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.BicomplexDiagonalComponents
import Mathlib.LinearAlgebra.TensorProduct.Pi

namespace OAI

/-! # Rationalization of the actual first-quadrant total complex

The finite antidiagonal makes tensoring commute with each total degree. The
comparison below keeps the rational scalar action and the signed differential.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory HomologicalComplex
open scoped TensorProduct
open Finset.HasAntidiagonal
attribute [local instance 2000] ModuleCat.isModule
attribute [local instance 2300] TensorProduct.instModule Pi.module

abbrev rationalBicomplex (K : NatBicomplex) : NatBicomplex ℚ :=
  (((rationalModuleFunctor.mapHomologicalComplex (ComplexShape.down ℕ)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj K)

variable (K : NatBicomplex)

def rationalTotalDegreeEquiv (n : ℕ) :
    (ℚ ⊗[ℤ] (K.total (ComplexShape.down ℕ)).X n) ≃ₗ[ℚ]
      ((rationalBicomplex K).total (ComplexShape.down ℕ)).X n := by
  classical
  exact (bicomplexDiagonalEquiv K n).baseChange ℤ ℚ _ _ ≪≫ₗ
    TensorProduct.piRight ℤ ℚ ℚ
      (fun p : ↥(antidiagonal n) => (K.X p.1.1).X p.1.2) ≪≫ₗ
    (bicomplexDiagonalEquiv (rationalBicomplex K) n).symm

theorem rationalTotalDegreeEquiv_tmul (n : ℕ) (a : ℚ)
    (x : (K.total (ComplexShape.down ℕ)).X n) :
    bicomplexToDiagonal (rationalBicomplex K) n
      (rationalTotalDegreeEquiv K n (a ⊗ₜ[ℤ] x)) =
        fun p => a ⊗ₜ[ℤ] bicomplexToDiagonal K n x p := by
  classical
  simp only [rationalTotalDegreeEquiv]
  exact (bicomplexDiagonalEquiv (rationalBicomplex K) n).apply_symm_apply _

theorem rationalTotalDegreeEquiv_d (n : ℕ)
    (x : ℚ ⊗[ℤ] (K.total (ComplexShape.down ℕ)).X (n + 1)) :
    rationalTotalDegreeEquiv K n
        ((((K.total (ComplexShape.down ℕ)).d (n + 1) n).hom.baseChange ℚ) x) =
      (((rationalBicomplex K).total (ComplexShape.down ℕ)).d (n + 1) n).hom
        (rationalTotalDegreeEquiv K (n + 1) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    apply (bicomplexDiagonalEquiv (rationalBicomplex K) n).injective
    change bicomplexToDiagonal (rationalBicomplex K) n
        (rationalTotalDegreeEquiv K n
          ((((K.total (ComplexShape.down ℕ)).d (n + 1) n).hom.baseChange ℚ) (a ⊗ₜ[ℤ] x))) =
      bicomplexToDiagonal (rationalBicomplex K) n
        ((((rationalBicomplex K).total (ComplexShape.down ℕ)).d (n + 1) n).hom
          (rationalTotalDegreeEquiv K (n + 1) (a ⊗ₜ[ℤ] x)))
    rw [LinearMap.baseChange_tmul, rationalTotalDegreeEquiv_tmul]
    erw [bicomplexToDiagonal_d (rationalBicomplex K) n]
    funext p
    rw [bicomplexToDiagonal_d, bicomplexDiagonalDifferential_apply,
      bicomplexDiagonalDifferential_apply]
    rw [rationalTotalDegreeEquiv_tmul]
    change a ⊗ₜ[ℤ] (_ + _) =
      (((K.d (p.1.1 + 1) p.1.1).f p.1.2).hom.baseChange ℚ)
        (a ⊗ₜ[ℤ] bicomplexToDiagonal K (n + 1) x (diagonalSucc₁ p)) +
      (-1 : ℤˣ) ^ p.1.1 •
        (((K.X p.1.1).d (p.1.2 + 1) p.1.2).hom.baseChange ℚ)
          (a ⊗ₜ[ℤ] bicomplexToDiagonal K (n + 1) x (diagonalSucc₂ p))
    simp only [LinearMap.baseChange_tmul, TensorProduct.tmul_add, Units.smul_def]
    congr 1
    exact map_zsmul (TensorProduct.mk ℤ ℚ _ a) _ _
  | add x y hx hy => simp only [map_add, hx, hy]

def rationalTotalComplexIso :
    ((rationalModuleFunctor.mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (K.total (ComplexShape.down ℕ))) ≅
        (rationalBicomplex K).total (ComplexShape.down ℕ) := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun n => (rationalTotalDegreeEquiv K n).toModuleIso) ?_
  intro i j hij
  have hi : j + 1 = i := hij
  subst i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (rationalTotalDegreeEquiv_d K j x).symm

end PolycyclicRecognition

end

end OAI
