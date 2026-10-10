import Mathlib.Analysis.Normed.Operator.Compact.Basic

namespace OAI

/-! Compactness passes to a linear map whose norm is controlled by a compact
map. This is used for the finite coordinate reconstruction of two-forms. -/

namespace PositiveEinsteinFour.Geometry

open Set Metric

noncomputable section

theorem compact_of_norm_domination
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (T : E →L[ℝ] F) (Q : E →L[ℝ] G) (hQ : IsCompactOperator Q)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, ‖T x‖ ≤ C * ‖Q x‖) :
    IsCompactOperator T := by
  let R := Set.range (Q : E → G)
  let pick : R → E := fun y => Classical.choose y.property
  have hpick (y : R) : Q (pick y) = y.val := Classical.choose_spec y.property
  let f : R → F := fun y => T (pick y)
  have hf (x : E) : f ⟨Q x, ⟨x, rfl⟩⟩ = T x := by
    have h := hb (pick ⟨Q x, ⟨x, rfl⟩⟩ - x)
    simp only [map_sub, hpick, sub_self, norm_zero, mul_zero] at h
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h)
  have hLip : LipschitzWith ⟨C, hC⟩ f := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (T (pick x)) (T (pick y)) ≤ C * dist x.val y.val
    simp only [dist_eq_norm]
    simpa only [map_sub, hpick] using hb (pick x - pick y)
  let B := closedBall (0 : E) 1
  have ht : TotallyBounded (Q '' B) :=
    (hQ.isCompact_closure_image_closedBall 1).totallyBounded.subset subset_closure
  have hs : TotallyBounded ((Subtype.val : R → G) ⁻¹' (Q '' B)) :=
    totallyBounded_preimage isUniformEmbedding_subtype_val.isUniformInducing ht
  have heq : f '' ((Subtype.val : R → G) ⁻¹' (Q '' B)) = T '' B := by
    ext z
    constructor
    · rintro ⟨y, ⟨x, hx, hxy⟩, rfl⟩
      refine ⟨x, hx, ?_⟩
      have hy : y = ⟨Q x, ⟨x, rfl⟩⟩ := Subtype.ext hxy.symm
      rw [hy, hf]
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨Q x, ⟨x, rfl⟩⟩, ⟨x, hx, rfl⟩, hf x⟩
  have htb : TotallyBounded (T '' B) := heq ▸ hs.image hLip.uniformContinuous
  exact (isCompactOperator_iff_isCompact_closure_image_closedBall
    T.toLinearMap (show (0 : ℝ) < 1 by norm_num)).mpr
      (isCompact_iff_totallyBounded_isComplete.mpr
        ⟨htb.closure, isClosed_closure.isComplete⟩)

theorem compact_finite_pi
    {E F J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype J]
    (Q : J → E →L[ℝ] F) (hQ : ∀ j, IsCompactOperator (Q j)) :
    IsCompactOperator (ContinuousLinearMap.pi Q) := by
  choose K hK hb using fun j => (hQ j).image_closedBall_subset_compact 1
  apply (isCompactOperator_iff_image_closedBall_subset_compact
    (ContinuousLinearMap.pi Q).toLinearMap (show (0 : ℝ) < 1 by norm_num)).mpr
  refine ⟨Set.pi Set.univ K, isCompact_univ_pi hK, ?_⟩
  rintro _ ⟨x, hx, rfl⟩ j _
  exact hb j ⟨x, hx, rfl⟩

end
end PositiveEinsteinFour.Geometry

end OAI
