import OAI.GroupTheory.PolycyclicRecognition.Analysis.AbelianMultilinearChains

namespace OAI

/-! # Multilinear evaluations descend to homology in every degree -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {A V : Type} [CommGroup A] [AddCommGroup V]

def abelianMultilinearHomology {n : ℕ}
    (F : MultilinearMap ℤ (fun _ : Fin n => Additive A) V) :
    groupHomology (integralTrivialCoefficient A) n →ₗ[ℤ] V := by
  let C := groupHomology.inhomogeneousChains (integralTrivialCoefficient A)
  let E : (C.sc n).X₂ ⟶ ModuleCat.of ℤ V := ModuleCat.ofHom (abelianMultilinearChains F)
  have hz : (C.sc n).toCycles ≫ ((C.sc n).iCycles ≫ E) = 0 := by
    rw [← Category.assoc, ShortComplex.toCycles_i]
    change C.d ((ComplexShape.down ℕ).prev n) n ≫ E = 0
    rw [(ComplexShape.down ℕ).prev_eq' (show (ComplexShape.down ℕ).Rel (n + 1) n from rfl)]
    rw [groupHomology.inhomogeneousChains.d_def]
    apply ModuleCat.hom_ext
    exact abelianMultilinearChains_boundary F
  exact ((C.sc n).descHomology ((C.sc n).iCycles ≫ E) hz).hom

theorem abelianMultilinearHomology_π {n : ℕ}
    (F : MultilinearMap ℤ (fun _ : Fin n => Additive A) V)
    (z : (groupHomology.inhomogeneousChains (integralTrivialCoefficient A)).cycles n) :
    abelianMultilinearHomology F (groupHomology.π (integralTrivialCoefficient A) n z) =
      abelianMultilinearChains F
        ((groupHomology.inhomogeneousChains (integralTrivialCoefficient A)).iCycles n z) := by
  let C := groupHomology.inhomogeneousChains (integralTrivialCoefficient A)
  let E : (C.sc n).X₂ ⟶ ModuleCat.of ℤ V := ModuleCat.ofHom (abelianMultilinearChains F)
  have hz : (C.sc n).toCycles ≫ ((C.sc n).iCycles ≫ E) = 0 := by
    rw [← Category.assoc, ShortComplex.toCycles_i]
    change C.d ((ComplexShape.down ℕ).prev n) n ≫ E = 0
    rw [(ComplexShape.down ℕ).prev_eq' (show (ComplexShape.down ℕ).Rel (n + 1) n from rfl)]
    rw [groupHomology.inhomogeneousChains.d_def]
    apply ModuleCat.hom_ext
    exact abelianMultilinearChains_boundary F
  exact congrArg (fun f : (C.sc n).cycles ⟶ ModuleCat.of ℤ V => f.hom z)
    ((C.sc n).π_descHomology ((C.sc n).iCycles ≫ E) hz)

end PolycyclicRecognition

end

end OAI
