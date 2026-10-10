import OAI.Analysis.KadisonKastler.InvariantOperatorMean

namespace OAI

/-! # Averaging operators preserving a projection nest

This is the algebraic averaging step after the nest distance estimate.
The projections may be indexed by any type; completeness of the nest is
needed by the distance theorem, not by these preservation calculations.
-/

namespace KadisonKastler

open scoped BoundedContinuousFunction

noncomputable section

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def PreservesProjectionNest (P : ι → H →L[ℂ] H) (T : H →L[ℂ] H) : Prop :=
  ∀ i, (1 - P i) * T * P i = 0

theorem preservesProjectionNest_conjugate
    (P : ι → H →L[ℂ] H) (T : H →L[ℂ] H) (u : unitary (H →L[ℂ] H))
    (hT : PreservesProjectionNest P T)
    (hP : ∀ i, ∃ j, P i = unitaryConj u (P j)) :
    PreservesProjectionNest P (unitaryConj u T) := by
  intro i
  obtain ⟨j, hj⟩ := hP i
  let e := Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) u
  change (1 - P i) * e T * P i = 0
  change P i = e (P j) at hj
  rw [hj, ← map_one e, ← map_sub, ← map_mul, ← map_mul, hT j, map_zero]

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]

theorem ScalarInvariantMean.operatorMean_zero_block
    (m : ScalarInvariantMean G) (A B : H →L[ℂ] H) (F : G →ᵇ (H →L[ℂ] H))
    (hF : ∀ g, A * F g * B = 0) : A * m.operatorMean F * B = 0 := by
  have he : BoundedContinuousFunction.const G A * F *
      BoundedContinuousFunction.const G B = 0 := by
    apply BoundedContinuousFunction.ext
    intro g
    exact hF g
  have h := congrArg m.operatorMean he
  rw [m.operatorMean_right, m.operatorMean_left, map_zero] at h
  exact h

theorem ScalarInvariantMean.operatorMean_preservesProjectionNest
    (m : ScalarInvariantMean G) (P : ι → H →L[ℂ] H)
    (F : G →ᵇ (H →L[ℂ] H)) (hF : ∀ g, PreservesProjectionNest P (F g)) :
    PreservesProjectionNest P (m.operatorMean F) :=
  fun i => m.operatorMean_zero_block (1 - P i) (P i) F (fun g => hF g i)

/-- Permuting the nest makes its algebra invariant under averaging. -/
theorem ScalarInvariantMean.averageConjugation_preservesProjectionNest
    (m : ScalarInvariantMean G) (P : ι → H →L[ℂ] H)
    (U : G →* unitary (H →L[ℂ] H)) (T : H →L[ℂ] H)
    (hT : PreservesProjectionNest P T)
    (hP : ∀ g i, ∃ j, P i = unitaryConj (U g) (P j)) :
    PreservesProjectionNest P (m.averageConjugation U T) := by
  apply m.operatorMean_preservesProjectionNest
  intro g
  exact preservesProjectionNest_conjugate P T (U g) hT (hP g)

/-- Averaging near a fixed target costs no additional error. -/
theorem ScalarInvariantMean.norm_averageConjugation_sub_fixed_le
    (m : ScalarInvariantMean G) (U : G →* unitary (H →L[ℂ] H))
    (T A : H →L[ℂ] H) (hA : ∀ g, unitaryConj (U g) A = A) :
    ‖m.averageConjugation U T - A‖ ≤ ‖T - A‖ := by
  have he : ScalarInvariantMean.conjugationFamily U T -
      BoundedContinuousFunction.const G A = ScalarInvariantMean.conjugationFamily U (T - A) := by
    ext g
    simp only [BoundedContinuousFunction.sub_apply, BoundedContinuousFunction.const_apply,
      ScalarInvariantMean.conjugationFamily_apply, unitaryConj_sub, hA]
  have hn : ‖ScalarInvariantMean.conjugationFamily U (T - A)‖ ≤ ‖T - A‖ := by
    apply (BoundedContinuousFunction.norm_le (norm_nonneg _)).mpr
    intro g
    exact (norm_unitaryConj (U g) (T - A)).le
  rw [ScalarInvariantMean.averageConjugation_apply, ← m.operatorMean_const A, ← map_sub, he]
  simp only [m.operatorMean_const]
  change ‖m.operator (ScalarInvariantMean.conjugationFamily U (T - A))‖ ≤ ‖T - A‖
  exact (m.norm_operator_le _).trans hn

end

end KadisonKastler

end OAI
