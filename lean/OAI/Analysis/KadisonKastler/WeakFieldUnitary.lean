import OAI.Analysis.KadisonKastler.WeakFieldCoefficients

namespace OAI

/-! # Unitary representatives of measurable operator classes

The AE-zero ideal has a useful lifting property: every unitary quotient
class has an everywhere unitary, weakly measurable representative. Only a
null set is changed, so no selection theorem is needed.
-/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {D H : Type*} [MeasurableSpace D] {μ : Measure D}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace WeakOperatorField

/-- A unitary operator class lifts to a unitary measurable representative. -/
theorem exists_unitary_lift (U : unitary (WeakOperatorField (H := H) μ)) :
    ∃ V : unitary (WeakOperatorRepresentative (H := H) μ),
      operatorFieldQuotient (H := H) μ (V : WeakOperatorRepresentative (H := H) μ) =
        (U : WeakOperatorField (H := H) μ) := by
  classical
  let R := representative (U : WeakOperatorField (H := H) μ)
  have hR : operatorFieldQuotient (H := H) μ R = (U : WeakOperatorField (H := H) μ) :=
    quotient_representative _
  have hleft : operatorFieldQuotient (H := H) μ (star R * R) = operatorFieldQuotient (H := H) μ 1 := by
    rw [map_mul, map_star, hR, Unitary.star_mul_self_of_mem U.property, map_one]
  have hright : operatorFieldQuotient (H := H) μ (R * star R) = operatorFieldQuotient (H := H) μ 1 := by
    rw [map_mul, map_star, hR, Unitary.mul_star_self_of_mem U.property, map_one]
  have hunit : ∀ᵐ x ∂μ, WeakOperatorRepresentative.eval R x ∈ unitary (H →L[ℂ] H) := by
    filter_upwards [(operatorFieldQuotient_eq_iff μ _ _).mp hleft,
      (operatorFieldQuotient_eq_iff μ _ _).mp hright] with x hl hr
    exact ⟨hl, hr⟩
  let f : D → H →L[ℂ] H := fun x =>
    if WeakOperatorRepresentative.eval R x ∈ unitary (H →L[ℂ] H)
      then WeakOperatorRepresentative.eval R x else 1
  have hfunit (x : D) : f x ∈ unitary (H →L[ℂ] H) := by
    dsimp [f]
    split_ifs with hx
    · exact hx
    · exact (unitary (H →L[ℂ] H)).one_mem
  have heq : WeakOperatorRepresentative.eval R =ᵐ[μ] f :=
    hunit.mono fun x hx => by simp only [f, ite_eq_left hx]
  have hm (ξ : H) : AEStronglyMeasurable (fun x => f x ξ) μ :=
    (WeakOperatorRepresentative.eval_aestronglyMeasurable R ξ).congr
      (heq.mono fun _ h => congrArg (fun T => T ξ) h)
  have hs (ξ : H) : AEStronglyMeasurable (fun x => star (f x) ξ) μ :=
    (WeakOperatorRepresentative.star_eval_aestronglyMeasurable R ξ).congr
      (heq.mono fun _ h => congrArg (fun T : H →L[ℂ] H => star T ξ) h)
  have hn (x : D) : ‖f x‖ ≤ 1 := norm_unitary_le_one ⟨f x, hfunit x⟩
  let F : WeakOperatorRepresentative (H := H) μ := WeakOperatorRepresentative.mk f 1 hn hm hs
  have hFU : F ∈ unitary (WeakOperatorRepresentative (H := H) μ) := by
    constructor
    · apply Subtype.ext
      apply BoundedContinuousFunction.ext
      intro x
      exact (hfunit x.ofTopology).1
    · apply Subtype.ext
      apply BoundedContinuousFunction.ext
      intro x
      exact (hfunit x.ofTopology).2
  refine ⟨⟨F, hFU⟩, ?_⟩
  exact ((operatorFieldQuotient_eq_iff μ R F).mpr heq).symm.trans hR

end WeakOperatorField

namespace WeakOperatorRepresentative

/-- Pointwise evaluation of a unitary representative is an actual unitary. -/
def unitaryEval (V : unitary (WeakOperatorRepresentative (H := H) μ)) (x : D) :
    unitary (H →L[ℂ] H) :=
  ⟨eval (V : WeakOperatorRepresentative (H := H) μ) x, by
    constructor
    · exact congrArg (fun F : WeakOperatorRepresentative (H := H) μ => eval F x)
        (Unitary.star_mul_self_of_mem V.property)
    · exact congrArg (fun F : WeakOperatorRepresentative (H := H) μ => eval F x)
        (Unitary.mul_star_self_of_mem V.property)⟩

theorem unitaryEval_measurable (V : unitary (WeakOperatorRepresentative (H := H) μ)) (ξ : H) :
    AEStronglyMeasurable (fun x => (unitaryEval V x : H →L[ℂ] H) ξ) μ :=
  eval_aestronglyMeasurable _ ξ

end WeakOperatorRepresentative

end

end KadisonKastler

end OAI
