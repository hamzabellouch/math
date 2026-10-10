import OAI.Analysis.KadisonKastler.WeightedStripCenter

namespace OAI

/-! # The extra strip weight has dense range and is injective -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}
  (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

include hsep hcyc in
theorem weightedStripOperator_center_injective :
    Function.Injective (weightedStripOperator (M := M) J Ω 0) := by
  have hq := one_sub_graphResolvent_injective J Ω hsep
  have hr := tomitaGraphRoot_injective J Ω hsep hcyc
  have hc : Function.Injective (tomitaGraphComplementRoot (M := M) J Ω) := by
    intro x y he
    apply hq
    rw [← tomitaGraphComplementRoot_square J Ω hsep hcyc]
    exact congrArg (tomitaGraphComplementRoot (M := M) J Ω) he
  rw [weightedStripOperator_center J Ω hsep hcyc]
  intro x y he
  apply hc
  apply hr
  apply hq
  apply hq
  apply graphResolvent_injective J Ω hsep hcyc
  simpa only [pow_two, mul_apply_eq_comp, tomitaMiddleOperator] using he

include hsep hcyc in
theorem weightedStripOperator_center_selfAdjoint :
    IsSelfAdjoint (weightedStripOperator (M := M) J Ω 0) := by
  let R := graphResolvent M J Ω 1
  let Q := 1 - R
  let T := tomitaMiddleOperator (M := M) J Ω
  have hRQ : Commute R Q := (Commute.one_right R).sub_right (Commute.refl R)
  have hTR : Commute T R := by
    change Commute (tomitaMiddleOperator (M := M) J Ω) (graphResolvent M J Ω 1)
    rw [← tomitaGraphRoot_square J Ω]
    have h : Commute (tomitaMiddleOperator (M := M) J Ω) (tomitaGraphRoot (M := M) J Ω) :=
      (Commute.refl _).mul_left (tomitaGraphRoots_commute J Ω).symm
    exact h.mul_right h
  have hTQ : Commute T Q := (Commute.one_right T).sub_right hTR
  rw [weightedStripOperator_center J Ω hsep hcyc]
  have hR : IsSelfAdjoint R := (graphResolvent_positive J Ω 1).isSelfAdjoint
  have hQ : IsSelfAdjoint Q := by
    change star (1 - R) = 1 - R
    rw [star_sub, star_one, hR.star_eq]
  have hD := (hR.commute_iff (hQ.pow 2)).mp (hRQ.pow_right 2)
  exact (hD.commute_iff (tomitaMiddleOperator_selfAdjoint J Ω)).mp
    (hTR.symm.mul_left (hTQ.pow_right 2).symm)

include hsep hcyc in
theorem weightedStripOperator_center_dense :
    DenseRange (weightedStripOperator (M := M) J Ω 0) := by
  let W := weightedStripOperator (M := M) J Ω 0
  change Dense (W.range : Set H)
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  apply Submodule.orthogonal_eq_bot_iff.mp
  rw [Submodule.orthogonal_closure, W.orthogonal_range]
  have hs : W.adjoint = W := (weightedStripOperator_center_selfAdjoint J Ω hsep hcyc).star_eq
  rw [hs]
  exact LinearMap.ker_eq_bot.mpr (weightedStripOperator_center_injective J Ω hsep hcyc)

include hsep hcyc in
theorem weightedStripOperator_cancel_sandwich (A B : H →L[ℂ] H)
    (he : weightedStripOperator (M := M) J Ω 0 * A * weightedStripOperator (M := M) J Ω 0 =
      weightedStripOperator (M := M) J Ω 0 * B * weightedStripOperator (M := M) J Ω 0) : A = B := by
  apply DFunLike.ext'
  apply (weightedStripOperator_center_dense J Ω hsep hcyc).equalizer A.continuous B.continuous
  funext x
  apply weightedStripOperator_center_injective J Ω hsep hcyc
  exact congrArg (fun T : H →L[ℂ] H => T x) he

end

end KadisonKastler

end OAI
