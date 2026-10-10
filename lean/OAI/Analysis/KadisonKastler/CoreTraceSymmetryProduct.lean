import OAI.Analysis.KadisonKastler.CoreTraceSymmetry

namespace OAI

/-! # Multiplication of vector-symmetric operators with commuting right actions -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (C : H ≃ₗᵢ⋆[ℂ] H) (hC : Function.Involutive C) (ξ : H)

include hC

theorem coreTraceSymmetry_of_vector (T : H →L[ℂ] H)
    (hT : T ξ = C ((star T) ξ)) : T ∈ coreTraceSymmetrySpace C ξ := by
  intro η
  have hc := conjugateIsometry_inner C (C η) ((star T) ξ)
  rw [hC η] at hc
  have hswap : star (inner ℂ (C η) ((star T) ξ)) =
      inner ℂ ((star T) ξ) (C η) := inner_conj_symm _ _
  rw [hswap] at hc
  rw [hT, hc, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]

theorem coreTraceSymmetry_vector (T : H →L[ℂ] H)
    (hT : T ∈ coreTraceSymmetrySpace C ξ) : T ξ = C ((star T) ξ) := by
  apply ext_inner_left ℂ
  intro η
  have hc := conjugateIsometry_inner C (C η) ((star T) ξ)
  rw [hC η] at hc
  have hswap : star (inner ℂ (C η) ((star T) ξ)) =
      inner ℂ ((star T) ξ) (C η) := inner_conj_symm _ _
  rw [hswap] at hc
  change inner ℂ η (T ξ) = inner ℂ η (C ((star T) ξ))
  rw [hc, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
  exact hT η

theorem coreTraceSymmetry_mul (hξ : C ξ = ξ) (A B : H →L[ℂ] H)
    (hA : A ∈ coreTraceSymmetrySpace C ξ) (hB : B ∈ coreTraceSymmetrySpace C ξ)
    (hcomm : Commute A (conjugationOperator C (star B))) :
    A * B ∈ coreTraceSymmetrySpace C ξ := by
  apply coreTraceSymmetry_of_vector C hC ξ
  have ha := coreTraceSymmetry_vector C hC ξ A hA
  have hb := coreTraceSymmetry_vector C hC ξ B hB
  have he := congrArg (fun T : H →L[ℂ] H => T ξ) hcomm.eq
  change A (C ((star B) (C ξ))) = C ((star B) (C (A ξ))) at he
  calc
    (A * B) ξ = A (B ξ) := rfl
    _ = A (C ((star B) ξ)) := congrArg A hb
    _ = C ((star B) (C (A ξ))) := by simpa only [hξ] using he
    _ = C ((star B) ((star A) ξ)) := by rw [ha, hC]
    _ = C ((star (A * B)) ξ) := by rw [star_mul]; rfl


theorem coreTraceSymmetry_compress (hξ : C ξ = ξ)
    (p T : H →L[ℂ] H) (hp : IsSelfAdjoint p) (hpξ : p ξ = ξ)
    (hTp : Commute T p) (hTq : Commute T (conjugationOperator C p))
    (hT : T ξ = C ((star T) ξ)) :
    p * T * p ∈ coreTraceSymmetrySpace C ξ := by
  apply coreTraceSymmetry_of_vector C hC ξ
  have hqξ : conjugationOperator C p ξ = ξ := by
    change C (p (C ξ)) = ξ
    rw [hξ, hpξ, hξ]
  have hleft : (p * T * p) ξ = T ξ := by
    change p (T (p ξ)) = T ξ
    rw [hpξ]
    exact (congrArg (fun A : H →L[ℂ] H => A ξ) hTp.symm.eq).trans
      (congrArg T hpξ)
  have hright : C ((star (p * T * p)) ξ) = T ξ := by
    rw [star_mul, star_mul, hp.star_eq]
    change C (p ((star T) (p ξ))) = T ξ
    rw [hpξ]
    have he := congrArg (fun A : H →L[ℂ] H => A ξ) hTq.eq
    change T (C (p (C ξ))) = C (p (C (T ξ))) at he
    rw [hξ, hpξ, hξ, hT, hC] at he
    exact he.symm.trans hT.symm
  exact hleft.trans hright.symm

end

end KadisonKastler

end OAI
