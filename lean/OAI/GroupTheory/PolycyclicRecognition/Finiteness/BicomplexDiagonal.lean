import OAI.GroupTheory.PolycyclicRecognition.Finiteness.ProjectiveCoefficientHomology
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.LinearAlgebra.Pi

namespace OAI

/-! # Finite coordinates for the first-quadrant total complex

Each total degree is the finite antidiagonal of the actual bicomplex. These
coordinates allow finite elimination, without assuming convergence of a
spectral sequence.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open scoped BigOperators
attribute [local instance 2000] ModuleCat.isModule
attribute [local instance 2300] Pi.module

abbrev NatBicomplex (R : Type := ℤ) [CommRing R] :=
  HomologicalComplex₂ (ModuleCat.{0} R) (ComplexShape.down ℕ) (ComplexShape.down ℕ)

abbrev bicomplexDiagonal {R : Type} [CommRing R] (K : NatBicomplex R) (n : ℕ) :=
  (p : ↥(Finset.HasAntidiagonal.antidiagonal n)) → (K.X p.1.1).X p.1.2

variable {R : Type} [CommRing R] (K : NatBicomplex R) (n : ℕ)

def bicomplexToDiagonal :
    (K.total (ComplexShape.down ℕ)).X n →ₗ[R] bicomplexDiagonal K n :=
  (K.totalDesc (c₁₂ := ComplexShape.down ℕ) (i₁₂ := n)
    (A := ModuleCat.of R (bicomplexDiagonal K n)) (fun i j h => ModuleCat.ofHom
    (LinearMap.single R
      (fun p : ↥(Finset.HasAntidiagonal.antidiagonal n) => (K.X p.1.1).X p.1.2)
      ⟨(i, j), Finset.HasAntidiagonal.mem_antidiagonal.mpr h⟩))).hom

def bicomplexFromDiagonal :
    bicomplexDiagonal K n →ₗ[R] (K.total (ComplexShape.down ℕ)).X n :=
  ∑ p : ↥(Finset.HasAntidiagonal.antidiagonal n),
    ((K.ιTotal (ComplexShape.down ℕ) p.1.1 p.1.2 n
      (Finset.HasAntidiagonal.mem_antidiagonal.mp p.2)).hom).comp (LinearMap.proj p)

theorem bicomplexToDiagonal_ι (p : ↥(Finset.HasAntidiagonal.antidiagonal n))
    (x : (K.X p.1.1).X p.1.2) :
    bicomplexToDiagonal K n
      ((K.ιTotal (ComplexShape.down ℕ) p.1.1 p.1.2 n
        (Finset.HasAntidiagonal.mem_antidiagonal.mp p.2)).hom x) = Pi.single p x := by
  have h := K.ι_totalDesc (c₁₂ := ComplexShape.down ℕ) (i₁₂ := n)
    (A := ModuleCat.of R (bicomplexDiagonal K n))
    (fun i j h => ModuleCat.ofHom
      (LinearMap.single R
        (fun p : ↥(Finset.HasAntidiagonal.antidiagonal n) => (K.X p.1.1).X p.1.2)
        ⟨(i, j), Finset.HasAntidiagonal.mem_antidiagonal.mpr h⟩))
    p.1.1 p.1.2 (Finset.HasAntidiagonal.mem_antidiagonal.mp p.2)
  exact congrArg (fun f => f.hom x) h

theorem bicomplexFromDiagonal_single (p : ↥(Finset.HasAntidiagonal.antidiagonal n))
    (x : (K.X p.1.1).X p.1.2) :
    bicomplexFromDiagonal K n (Pi.single p x) =
      (K.ιTotal (ComplexShape.down ℕ) p.1.1 p.1.2 n
        (Finset.HasAntidiagonal.mem_antidiagonal.mp p.2)).hom x := by
  classical
  simp only [bicomplexFromDiagonal, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply]
  rw [Finset.sum_eq_single p]
  · rw [Pi.single_eq_same]
  · intro q _ hq
    rw [Pi.single_eq_of_ne hq, map_zero]
  · simp

theorem bicomplexToFromDiagonal (x : bicomplexDiagonal K n) :
    bicomplexToDiagonal K n (bicomplexFromDiagonal K n x) = x := by
  classical
  simp only [bicomplexFromDiagonal, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, map_sum, bicomplexToDiagonal_ι]
  exact LinearMap.sum_single_apply _ x

theorem bicomplexFromToDiagonal
    (x : (K.total (ComplexShape.down ℕ)).X n) :
    bicomplexFromDiagonal K n (bicomplexToDiagonal K n x) = x := by
  have h : ModuleCat.ofHom ((bicomplexFromDiagonal K n).comp
      (bicomplexToDiagonal K n)) = 𝟙 _ := by
    apply HomologicalComplex₂.total.hom_ext
    intro i j hij
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change bicomplexFromDiagonal K n
      (bicomplexToDiagonal K n ((K.ιTotal _ i j n hij).hom a)) = _
    have hp : (i, j) ∈ Finset.HasAntidiagonal.antidiagonal n := Finset.HasAntidiagonal.mem_antidiagonal.mpr hij
    rw [bicomplexToDiagonal_ι K n ⟨(i, j), hp⟩,
      bicomplexFromDiagonal_single]
    rfl
  exact congrArg (fun f => f.hom x) h

def bicomplexDiagonalEquiv :
    (K.total (ComplexShape.down ℕ)).X n ≃ₗ[R] bicomplexDiagonal K n :=
  LinearEquiv.ofLinearMap (bicomplexToDiagonal K n) (bicomplexFromDiagonal K n)
    (LinearMap.ext (bicomplexToFromDiagonal K n))
    (LinearMap.ext (bicomplexFromToDiagonal K n))

end PolycyclicRecognition

end

end OAI
