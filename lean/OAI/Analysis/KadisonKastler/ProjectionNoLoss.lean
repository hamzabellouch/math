import OAI.Analysis.KadisonKastler.RowVarianceEquality

namespace OAI

/-! Zero loss for projection rows forces exact right modularity. -/

namespace KadisonKastler

noncomputable section

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem projectionAverage_fixed_of_no_loss {M : VonNeumannAlgebra H}
    (F : Algebra M →ₗ[ℂ] Algebra M) {p : Algebra M} (hp : IsStarProjection p)
    (hloss : ∀ (a : Algebra M) (ξ : H),
      rowEnergy F (fun i => a * projectionRow p i) ξ =
        ‖(star (projectionAverage p F a) : H →L[ℂ] H) ξ‖ ^ 2) :
    projectionAverage p F = F := by
  apply LinearMap.ext
  intro a
  apply star_injective
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro ξ
  let η := (star (projectionAverage p F a) : H →L[ℂ] H) ξ
  have hps : star (p : H →L[ℂ] H) = p :=
    (hp.map M.toStarSubalgebra.subtype).isSelfAdjoint.star_eq
  have hqs : star ((1 - p : Algebra M) : H →L[ℂ] H) = (1 - p : Algebra M) :=
    (hp.one_sub.map M.toStarSubalgebra.subtype).isSelfAdjoint.star_eq
  have hfalse : (star (F (a * p)) : H →L[ℂ] H) ξ = (p : H →L[ℂ] H) η := by
    have h := finiteRightAverage_no_loss (projectionRow p) (projectionRow_normalized hp)
      F a ξ (hloss a ξ) false
    simpa only [projectionRow, Bool.false_eq_true, ite_false, hps, η, projectionAverage] using h
  have htrue : (star (F (a * (1 - p))) : H →L[ℂ] H) ξ =
      ((1 - p : Algebra M) : H →L[ℂ] H) η := by
    have h := finiteRightAverage_no_loss (projectionRow p) (projectionRow_normalized hp)
      F a ξ (hloss a ξ) true
    simpa only [projectionRow, ite_true, hqs, η, projectionAverage] using h
  have hsum : F (a * p) + F (a * (1 - p)) = F a := by
    rw [← map_add, ← mul_add, add_sub_cancel, mul_one]
  change η = (star (F a) : H →L[ℂ] H) ξ
  rw [← hsum]
  simp only [AddMemClass.coe_add, star_add, add_apply]
  change η = (star (F (a * p)) : H →L[ℂ] H) ξ +
    (star (F (a * (1 - p))) : H →L[ℂ] H) ξ
  rw [hfalse, htrue]
  simp only [AddSubgroupClass.coe_sub, OneMemClass.coe_one, sub_apply,
    one_apply_eq_self]
  abel

theorem right_module_of_projection_no_loss (M : VonNeumannAlgebra H)
    (F : Algebra M →L[ℂ] Algebra M)
    (hloss : ∀ (p : Algebra M), IsStarProjection p → ∀ (a : Algebra M) (ξ : H),
      rowEnergy F.toLinearMap (fun i => a * projectionRow p i) ξ =
        ‖(star (projectionAverage p F.toLinearMap a) : H →L[ℂ] H) ξ‖ ^ 2) :
    ∀ a b, F (a * b) = F a * b := by
  apply (right_module_iff_projectionAverage_fixed M F).2
  intro p hp
  exact projectionAverage_fixed_of_no_loss F.toLinearMap hp (hloss p hp)

end

end KadisonKastler

end OAI
