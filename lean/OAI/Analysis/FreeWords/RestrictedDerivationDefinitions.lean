import Mathlib

namespace OAI

noncomputable section

namespace KKMatrixHilbert

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def restrictedDerivation (S : StarSubalgebra ℂ (H →L[ℂ] H)) (h : H →L[ℂ] H) :
    S →L[ℂ] (H →L[ℂ] H) where
  toFun a := h * (a : H →L[ℂ] H) - (a : H →L[ℂ] H) * h
  map_add' := by
    intro a b
    change h * ((a:H →L[ℂ] H)+(b:H →L[ℂ] H)) - ((a:H →L[ℂ] H)+(b:H →L[ℂ] H)) * h = _
    noncomm_ring
  map_smul' := by intro scalar operator; simp [smul_sub]
  cont := by fun_prop

end

end KKMatrixHilbert
end

end OAI
