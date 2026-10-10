import OAI.GroupTheory.PolycyclicRecognition.Finiteness.BicomplexTotalExact

namespace OAI

/-! # Naturality of finite antidiagonal coordinates -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open scoped BigOperators
open Finset.HasAntidiagonal
attribute [local instance 2000] ModuleCat.isModule
attribute [local instance 2300] Pi.module

variable {K L : NatBicomplex} (f : K ⟶ L) (n : ℕ)

def bicomplexDiagonalMap : bicomplexDiagonal K n →ₗ[ℤ] bicomplexDiagonal L n :=
  LinearMap.pi (fun p => (((f.f p.1.1).f p.1.2).hom).comp (LinearMap.proj p))

theorem bicomplexTotalMap_ι (p : ↥(antidiagonal n)) (x : (K.X p.1.1).X p.1.2) :
    ((HomologicalComplex₂.total.map f (ComplexShape.down ℕ)).f n).hom
      ((K.ιTotal (ComplexShape.down ℕ) p.1.1 p.1.2 n (mem_antidiagonal.mp p.2)).hom x) =
    (L.ιTotal (ComplexShape.down ℕ) p.1.1 p.1.2 n (mem_antidiagonal.mp p.2)).hom
      (((f.f p.1.1).f p.1.2).hom x) :=
  congrArg (fun g => g.hom x)
    (HomologicalComplex₂.ιTotal_map K L f (ComplexShape.down ℕ)
      p.1.1 p.1.2 n (mem_antidiagonal.mp p.2))

theorem bicomplexToDiagonal_natural (x : (K.total (ComplexShape.down ℕ)).X n) :
    bicomplexToDiagonal L n
      (((HomologicalComplex₂.total.map f (ComplexShape.down ℕ)).f n).hom x) =
      bicomplexDiagonalMap f n (bicomplexToDiagonal K n x) := by
  classical
  have hgen : ∀ p : ↥(antidiagonal n), ∀ z : (K.X p.1.1).X p.1.2,
      bicomplexToDiagonal L n
        (((HomologicalComplex₂.total.map f (ComplexShape.down ℕ)).f n).hom
          ((K.ιTotal (ComplexShape.down ℕ) p.1.1 p.1.2 n (mem_antidiagonal.mp p.2)).hom z)) =
      Pi.single p (((f.f p.1.1).f p.1.2).hom z) := by
    intro p z
    rw [bicomplexTotalMap_ι, bicomplexToDiagonal_ι]
  conv_lhs => rw [← bicomplexFromToDiagonal K n x]
  simp only [bicomplexFromDiagonal, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, map_sum, hgen]
  change (∑ p, Pi.single p
    ((bicomplexDiagonalMap f n) (bicomplexToDiagonal K n x) p)) = _
  exact LinearMap.sum_single_apply _ _

end PolycyclicRecognition

end

end OAI
