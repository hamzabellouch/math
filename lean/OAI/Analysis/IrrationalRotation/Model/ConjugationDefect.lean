import OAI.Analysis.IrrationalRotation.Model.Conjugation
import Mathlib.Analysis.InnerProductSpace.Adjoint
import OAI.Analysis.IrrationalRotation.Model.Analytic

namespace OAI

noncomputable section
open scoped BigOperators

namespace Invariant233

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]

abbrev HilbertConjugation :=
  {C : H ≃ₗᵢ⋆[ℂ] H // Function.Involutive C}

variable {H}

def IsConjugation.toHilbertConjugation {C : H → H} (hC : IsConjugation C) :
    HilbertConjugation H :=
  ⟨{ toFun := C
     invFun := C
     left_inv := hC.1
     right_inv := hC.1
     map_add' := hC.2.1
     map_smul' := hC.2.2.1
     norm_map' := hC.2.2.2 }, hC.1⟩

def HilbertConjugation.conjugate (C : HilbertConjugation H) (T : H →L[ℂ] H) :
    H →L[ℂ] H :=
  (((C.val : H →L⋆[ℂ] H).comp T).comp (C.val : H →L⋆[ℂ] H))

variable [CompleteSpace H]

def conjugationDefect (C : HilbertConjugation H) (T : H →L[ℂ] H) (m : ℕ) :
    H →L[ℂ] H :=
  ∑ j ∈ Finset.range (m + 1),
    ((-1 : ℂ) ^ j * (m.choose j : ℂ)) •
      ((star T) ^ (m - j) * C.conjugate (T ^ (m - j)))

def IsInfiniteConjugationIsometry (C : HilbertConjugation H) (T : H →L[ℂ] H) : Prop :=
  Filter.Tendsto (fun m : ℕ => ‖conjugationDefect C T m‖ ^ (1 / (m : ℝ)))
    Filter.atTop (nhds 0)

end Invariant233

end

end OAI
