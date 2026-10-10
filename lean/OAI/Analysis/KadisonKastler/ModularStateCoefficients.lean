import OAI.Analysis.KadisonKastler.ModularStateAction

namespace OAI

/-! # Matrix coefficients of a vector-fixing unitary action -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem star_unitary_fixes (Ω : H) (u : unitary (H →L[ℂ] H))
    (hfix : (u : H →L[ℂ] H) Ω = Ω) : star (u : H →L[ℂ] H) Ω = Ω := by
  calc
    _ = star (u : H →L[ℂ] H) ((u : H →L[ℂ] H) Ω) := by rw [hfix]
    _ = Ω := congrArg (fun T : H →L[ℂ] H => T Ω) (Unitary.star_mul_self_of_mem u.property)

theorem productVectorState_conjugate_left (Ω : H) (u : unitary (H →L[ℂ] H))
    (hfix : (u : H →L[ℂ] H) Ω = Ω) (x y : H →L[ℂ] H) :
    productVectorState Ω (unitaryConj u x * y) =
      inner ℂ (star x Ω) (star (u : H →L[ℂ] H) (y Ω)) := by
  change inner ℂ Ω ((u : H →L[ℂ] H) (x (star (u : H →L[ℂ] H) (y Ω)))) = _
  rw [← ContinuousLinearMap.adjoint_inner_left]
  change inner ℂ (star (u : H →L[ℂ] H) Ω) (x (star (u : H →L[ℂ] H) (y Ω))) = _
  rw [star_unitary_fixes Ω u hfix]
  exact (ContinuousLinearMap.adjoint_inner_left x _ Ω).symm

theorem productVectorState_conjugate_right (Ω : H) (u : unitary (H →L[ℂ] H))
    (hfix : (u : H →L[ℂ] H) Ω = Ω) (x y : H →L[ℂ] H) :
    productVectorState Ω (y * unitaryConj u x) =
      inner ℂ (star y Ω) ((u : H →L[ℂ] H) (x Ω)) := by
  change inner ℂ Ω (y ((u : H →L[ℂ] H) (x (star (u : H →L[ℂ] H) Ω)))) = _
  rw [star_unitary_fixes Ω u hfix]
  exact (ContinuousLinearMap.adjoint_inner_left y _ Ω).symm

end

end KadisonKastler

end OAI
