import Mathlib
import OAI.Analysis.FreeWords.TraceTransferDefinitions

namespace OAI

noncomputable section

namespace KKTraceTransfer

open scoped InnerProductSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem traceNorm_strong_continuous {X : Type*} [TopologicalSpace X]
    (M : VonNeumannAlgebra H) (τ : FaithfulNormalTrace M)
    (F : X → ConcreteAlgebra M) (hF : ∀ a, ‖F a‖ ≤ 1)
    (hc : ∀ ξ : H, Continuous (fun a => (F a : H →L[ℂ] H) ξ))
    (b : ConcreteAlgebra M) (hb : ‖b‖ ≤ 1) :
    Continuous (fun a => traceNorm τ (F a-b)) := by
  let Q (a:X) : ConcreteAlgebra M := star (F a-b)*(F a-b)
  let W (a:X) : WeakAlgebra M := ⟨ContinuousLinearMapWOT.ofCLM (Q a), (Q a).property⟩
  have hB (a:X) : ‖(W a).val.toCLM‖ ≤ 4 := by
    have hs : ‖F a-b‖ ≤ 2 := (norm_sub_le _ _).trans (by linarith [hF a])
    change ‖star ((F a-b : ConcreteAlgebra M):H →L[ℂ] H) * ((F a-b:ConcreteAlgebra M):H →L[ℂ] H)‖ ≤ 4
    rw [CStarRing.norm_star_mul_self]
    change ‖F a-b‖*‖F a-b‖ ≤ 4
    nlinarith [norm_nonneg (F a-b)]
  have hW : Continuous W := by
    apply Continuous.subtype_mk
    apply ContinuousLinearMapWOT.continuous_iff.mpr
    intro ξ η
    change Continuous (fun a => ⟪η, (star ((F a-b :ConcreteAlgebra M):H →L[ℂ] H) *
      ((F a-b :ConcreteAlgebra M):H →L[ℂ] H)) ξ⟫_ℂ)
    simp only [mul_apply_eq_comp,ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right]
    exact ((hc η).sub continuous_const).inner ((hc ξ).sub continuous_const)
  have hτ := (τ.normal 4).comp_continuous hW hB
  exact Real.continuous_sqrt.comp (Complex.continuous_re.comp hτ)

end

end KKTraceTransfer
end

end OAI
