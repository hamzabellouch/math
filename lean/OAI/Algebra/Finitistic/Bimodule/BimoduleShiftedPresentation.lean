import OAI.Algebra.Finitistic.Bimodule.BimoduleBoundedPresentation
import OAI.Algebra.Finitistic.Ordinary.OrdinaryShiftDerivedTensor

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.BimoduleTotalPresentation
open ExternalTensor.Section4
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable (P : BiComplex k B) (b : ℤ) (length : ℕ)
variable [∀ n, Module.Projective Bᵐᵒᵖ ((OrdinarySimulation.underlyingRightComplex P).X n)]

local instance : ∀ n, Module.Projective Bᵐᵒᵖ
    (ComplexTensor.rightTerm k B (BimoduleTotal.right k B (P⟦b⟧)) n) :=
  fun n => inferInstanceAs (Module.Projective Bᵐᵒᵖ
    ((OrdinarySimulation.underlyingRightComplex P).X (n+b)))

variable [HasDerivedCategory.{u+1} (ModuleCat.{u} B)]
variable (data : BimoduleTotal.BoundedProjective k B (P⟦b⟧))

/-- The ordinary shifted-derived API agrees with any native model of the identical
shifted complex on [-length,0]. No shift-left tensor theorem is reproved or assumed. -/
def shiftedDerivedIso (hlo : data.lower = -(length : ℤ)) (hhi : data.upper = 0) :
    OrdinarySimulation.shiftedDerivedTensor P b length ≅ data.derived :=
  boundedNonpositiveDerivedIso k B (P⟦b⟧) data length hlo hhi

/-- The same comparison on every actual shifted-derived iterate. -/
def shiftedPowerIso (hlo : data.lower = -(length : ℤ)) (hhi : data.upper = 0)
    (r : ℕ) (Y : DerivedCategory (ModuleCat.{u} B)) :
    ((OrdinarySimulation.shiftedDerivedTensor P b length).obj^[r]) Y ≅
      (data.derived.obj^[r]) Y :=
  powerObjIso (shiftedDerivedIso P b length data hlo hhi) r Y
end LittleFinitistic.BimoduleTotalPresentation

end

end OAI
