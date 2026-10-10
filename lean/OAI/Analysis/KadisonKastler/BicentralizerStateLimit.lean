import OAI.Analysis.KadisonKastler.BicentralizerStateCauchy
import OAI.Analysis.KadisonKastler.ReferenceStrongLimit

namespace OAI

/-! # Strong limits of bicentralizer state conjugates -/

namespace KadisonKastler

open Generator.Tracial Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem exists_bicentralizer_state_conjugate_limit (ξ η : H)
    (hξ : Function.Injective (algebraVectorMap M ξ))
    (hη : Function.Injective (algebraVectorMap M η))
    (a : Algebra M) (ha : stateBicentralizerMember ξ a)
    (u : ℕ → unitary (Algebra M))
    (hu : Tendsto (fun n =>
      ‖sandwichFunctional (vectorFunctional ξ) (u n).val-vectorFunctional η‖) atTop (𝓝 0)) :
    ∃ b : Algebra M, ‖b‖ ≤ ‖a‖ ∧
      ∀ ζ : H, Tendsto (fun n => ((u n).val*a*star (u n).val).val ζ) atTop
        (𝓝 (b.val ζ)) := by
  apply exists_algebra_strong_limit_of_reference_cauchy η hη
    (fun n => (u n).val*a*star (u n).val) ‖a‖ (norm_nonneg _)
  · intro n
    change ‖(u n).val*a*(star (u n)).val‖ ≤ ‖a‖
    exact le_of_eq (by
      rw [CStarRing.norm_mul_coe_unitary,CStarRing.norm_coe_unitary_mul])
  · exact stateBicentralizerMember.conjugates_cauchy ξ η hξ a ha u hu

end

end KadisonKastler

end OAI
