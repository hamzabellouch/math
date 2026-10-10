import OAI.Analysis.KadisonKastler.BicentralizerProjection
import OAI.Analysis.KadisonKastler.StateBicentralizerVonNeumann
import OAI.Analysis.KadisonKastler.StatePreservingWeakLimit

namespace OAI

/-! # The state-preserving bicentralizer retraction

The constructed contractive projection has the actual bicentralizer as
codomain. Tomiyama's projection identities make it bimodular; normality is not required.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem stateBicentralizerVonNeumann_le (ξ : H)
    (hsep : Function.Injective (algebraVectorMap M ξ)) :
    stateBicentralizerVonNeumann ξ hsep ≤ M := concreteStateBicentralizer_le ξ hsep

def bicentralizerExpectation (ξ : H)
    (hsep : Function.Injective (algebraVectorMap M ξ)) :
    Algebra M →L[ℂ] Algebra (stateBicentralizerVonNeumann ξ hsep) :=
  (M.toStarSubalgebra.toSubalgebra.toSubmodule.subtypeL.comp
    (bicentralizerProjectionCLM ξ hsep)).codRestrict
      (stateBicentralizerVonNeumann ξ hsep).toStarSubalgebra.toSubalgebra.toSubmodule
      (fun a => (mem_stateBicentralizerVonNeumann ξ hsep _).mpr
        (bicentralizerProjection_mem ξ hsep a))

theorem bicentralizerExpectation_val (ξ : H)
    (hsep : Function.Injective (algebraVectorMap M ξ)) (a : Algebra M) :
    (bicentralizerExpectation ξ hsep a).val=(bicentralizerProjectionCLM ξ hsep a).val := rfl

theorem bicentralizerExpectation_norm_le (ξ : H)
    (hsep : Function.Injective (algebraVectorMap M ξ)) : ‖bicentralizerExpectation ξ hsep‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro a
  change ‖bicentralizerProjection ξ hsep a‖ ≤ 1*‖a‖
  simpa only [one_mul] using bicentralizerProjection_norm_le ξ hsep a

theorem bicentralizerExpectation_fixed (ξ : H)
    (hsep : Function.Injective (algebraVectorMap M ξ))
    (a : Algebra (stateBicentralizerVonNeumann ξ hsep)) :
    bicentralizerExpectation ξ hsep
      (coordinateInclusion (stateBicentralizerVonNeumann_le ξ hsep) a)=a := by
  apply Subtype.ext
  rw [bicentralizerExpectation_val]
  exact congrArg Subtype.val (bicentralizerProjection_fixed ξ hsep _
    ((mem_stateBicentralizerVonNeumann ξ hsep _).mp a.property))

theorem bicentralizerExpectation_bimodule (ξ : H)
    (hsep : Function.Injective (algebraVectorMap M ξ)) :
    (∀ (b : Algebra (stateBicentralizerVonNeumann ξ hsep)) (a : Algebra M),
      bicentralizerExpectation ξ hsep
        (coordinateInclusion (stateBicentralizerVonNeumann_le ξ hsep) b*a)=
        b*bicentralizerExpectation ξ hsep a) ∧
    (∀ (b : Algebra (stateBicentralizerVonNeumann ξ hsep)) (a : Algebra M),
      bicentralizerExpectation ξ hsep
        (a*coordinateInclusion (stateBicentralizerVonNeumann_le ξ hsep) b)=
        bicentralizerExpectation ξ hsep a*b) :=
  retraction_bimodule (stateBicentralizerVonNeumann_le ξ hsep)
    (bicentralizerExpectation ξ hsep) (bicentralizerExpectation_norm_le ξ hsep)
    (bicentralizerExpectation_fixed ξ hsep)

theorem bicentralizerExpectation_state (ξ : H)
    (hsep : Function.Injective (algebraVectorMap M ξ)) (a : Algebra M) :
    vectorFunctional ξ (bicentralizerExpectation ξ hsep a)=vectorFunctional ξ a :=
  bicentralizerProjection_state ξ hsep a

theorem bicentralizerExpectation_faithful (ξ : H)
    (hsep : Function.Injective (algebraVectorMap M ξ)) (a : Algebra M)
    (ha : bicentralizerExpectation ξ hsep (star a*a)=0) : a=0 := by
  have hφ := bicentralizerExpectation_state ξ hsep (star a*a)
  rw [ha,map_zero] at hφ
  have hnorm : ‖a.val ξ‖^2=0 := by
    have h := hφ.symm
    rw [vectorFunctional_star_mul_self] at h
    exact_mod_cast h
  have hv : a.val ξ=0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)
  apply hsep
  simpa only [algebraVectorMap,LinearMap.coe_mk,AddHom.coe_mk,ZeroMemClass.coe_zero,
    zero_apply] using hv

end

end KadisonKastler

end OAI
