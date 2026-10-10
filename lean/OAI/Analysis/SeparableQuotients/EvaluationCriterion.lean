import OAI.Analysis.SeparableQuotients.FiniteNormers

namespace OAI

namespace SeparableQuotient
open Set Metric
open scoped Topology BigOperators
universe u
variable {𝕜 : Type} [RCLike 𝕜]
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
@[reducible] noncomputable local instance evaluationCriterionDualNormedGroup :
    NormedAddCommGroup (StrongDual 𝕜 X) := inferInstance
@[reducible] noncomputable local instance evaluationCriterionDualNormedSpace :
    NormedSpace 𝕜 (StrongDual 𝕜 X) := inferInstance

@[reducible] noncomputable local instance evaluationCriterionSubspaceDualNormedGroup
    (F : Submodule 𝕜 (StrongDual 𝕜 X)) : NormedAddCommGroup (StrongDual 𝕜 F) := inferInstance
@[reducible] noncomputable local instance evaluationCriterionSubspaceDualNormedSpace
    (F : Submodule 𝕜 (StrongDual 𝕜 X)) : NormedSpace 𝕜 (StrongDual 𝕜 F) := inferInstance

/-- Norm-separable evaluation on an infinite-dimensional dual subspace yields a separable quotient. -/
theorem hasSeparableQuotient_of_separable_evaluation
    (F : Submodule 𝕜 (StrongDual 𝕜 X)) [IsClosed (F : Set (StrongDual 𝕜 X))]
    (hF : ¬ FiniteDimensional 𝕜 F)
    (hsep : TopologicalSpace.IsSeparable (Set.range (subspaceEvaluation F))) :
    HasSeparableQuotient 𝕜 X := by
  classical
  obtain ⟨xs, hxs⟩ := exists_dense_evaluations F hsep
  let f := NormerStep.seq F hF xs
  let H := NormerStep.prefixNormers F hF xs
  have hn : ∀ n, (1 : ℝ) ≤ ‖f n‖ := fun n => (NormerStep.seq_norm F hF xs n).ge
  let G := PrefixNormers.closedSpan f
  let Z := H.coefficientSpan 1 (by norm_num) hn
  let inc : G →L[𝕜] F := G.subtypeL.codRestrict F
    (fun v => NormerStep.span_le F hF xs v.property)
  let restriction : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 G :=
    ContinuousLinearMap.precomp 𝕜 inc
  have he (x : X) : restriction (subspaceEvaluation F x) = PrefixNormers.evaluation f x := by
    ext v; rfl
  have hx (j : ℕ) : restriction (subspaceEvaluation F (xs j)) ∈ Z := by
    rw [he]
    change PrefixNormers.evaluation (NormerStep.seq F hF xs) (xs j) ∈ Z
    rw [NormerStep.evaluation_x]
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.smul_mem
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span (Set.mem_range_self i))
  have hc : IsClosed (restriction ⁻¹' (Z : Set (StrongDual 𝕜 G))) :=
    (H.coefficientSpan_isClosed 1 (by norm_num) hn).preimage restriction.continuous
  apply H.hasSeparableQuotient_of_range 1 (by norm_num) hn
  intro x
  rw [← he x]
  apply closure_minimal (t := restriction ⁻¹' (Z : Set (StrongDual 𝕜 G))) ?_ hc (hxs x)
  rintro _ ⟨j, rfl⟩
  exact hx j

end SeparableQuotient

namespace SeparableQuotient
open Set Metric
open scoped Topology
universe u
variable {𝕜 : Type} [RCLike 𝕜]
variable {X Y : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]
@[reducible] noncomputable local instance necessityDualGroup (E : Type u)
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] : NormedAddCommGroup (StrongDual 𝕜 E) :=
  inferInstance
@[reducible] noncomputable local instance necessityDualSpace (E : Type u)
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] : NormedSpace 𝕜 (StrongDual 𝕜 E) :=
  inferInstance

omit [CompleteSpace Y] in
/-- The dual of an infinite-dimensional normed space is infinite-dimensional. -/
lemma dual_infiniteDimensional (hY : ¬ FiniteDimensional 𝕜 Y) :
    ¬ FiniteDimensional 𝕜 (StrongDual 𝕜 Y) := by
  intro h
  let := h
  apply hY
  exact FiniteDimensional.of_injective (NormedSpace.inclusionInDoubleDualLi 𝕜).toLinearMap
    (NormedSpace.inclusionInDoubleDualLi 𝕜).injective

/-- The adjoint of an onto map is bounded below, with the actual open-mapping lift constant. -/
lemma precomp_antilipschitz_of_surjective (T : X →L[𝕜] Y) (hT : Function.Surjective T) :
    ∃ C : NNReal, AntilipschitzWith C
      (ContinuousLinearMap.precomp 𝕜 T : StrongDual 𝕜 Y →L[𝕜] StrongDual 𝕜 X) := by
  obtain ⟨g, _hg⟩ := T.exists_nonlinearRightInverse_of_surjective (LinearMap.range_eq_top.mpr hT)
  let S : StrongDual 𝕜 Y →L[𝕜] StrongDual 𝕜 X := ContinuousLinearMap.precomp 𝕜 T
  refine ⟨g.nnnorm, S.antilipschitz_of_bound ?_⟩
  intro f
  apply f.opNorm_le_bound (mul_nonneg g.nnnorm.coe_nonneg (norm_nonneg _))
  intro y
  calc
    ‖f y‖ = ‖S f (g y)‖ := by
      change ‖f y‖ = ‖f (T (g y))‖
      rw [g.right_inv]
    _ ≤ ‖S f‖ * ‖g y‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖S f‖ * (g.nnnorm * ‖y‖) :=
      mul_le_mul_of_nonneg_left (g.bound y) (norm_nonneg _)
    _ = (g.nnnorm * ‖S f‖) * ‖y‖ := by ring

/-- A separable quotient yields an infinite-dimensional dual subspace with norm-separable evaluation. -/
theorem separable_evaluation_of_hasSeparableQuotient (hX : HasSeparableQuotient 𝕜 X) :
    ∃ F : Submodule 𝕜 (StrongDual 𝕜 X), IsClosed (F : Set (StrongDual 𝕜 X)) ∧
      (¬ FiniteDimensional 𝕜 F) ∧
      TopologicalSpace.IsSeparable (Set.range (subspaceEvaluation F)) := by
  obtain ⟨Y, hYn, hYs, hYc, hYsep, hYinf, T, hT⟩ := hX
  let := hYn
  let := hYs
  let := hYc
  let := hYsep
  let S : StrongDual 𝕜 Y →L[𝕜] StrongDual 𝕜 X := ContinuousLinearMap.precomp 𝕜 T
  obtain ⟨C, hC⟩ := precomp_antilipschitz_of_surjective T hT
  have hSc : IsClosed (Set.range S) := hC.isClosed_range S.uniformContinuous
  let F := S.range
  have hFc : IsClosed (F : Set (StrongDual 𝕜 X)) := hSc
  let e : StrongDual 𝕜 Y ≃L[𝕜] F := S.equivRange hC.injective hSc
  have hFi : ¬ FiniteDimensional 𝕜 F := by
    intro hf
    let := hf
    have : FiniteDimensional 𝕜 (StrongDual 𝕜 Y) := e.toLinearEquiv.symm.finiteDimensional
    exact dual_infiniteDimensional hYinf inferInstance
  let Q : Y →L[𝕜] StrongDual 𝕜 F :=
    (ContinuousLinearMap.precomp 𝕜 e.symm.toContinuousLinearMap).comp
      (NormedSpace.inclusionInDoubleDual 𝕜 Y)
  have he (x : X) : subspaceEvaluation F x = Q (T x) := by
    ext f
    obtain ⟨g, rfl⟩ := e.surjective f
    change (S g) x = (e.symm (e g)) (T x)
    rw [e.symm_apply_apply]
    rfl
  refine ⟨F, hFc, hFi, (TopologicalSpace.isSeparable_range Q.continuous).mono ?_⟩
  rintro _ ⟨x, rfl⟩
  exact ⟨T x, (he x).symm⟩

/-- Exact evaluation criterion over either scalar field. -/
theorem hasSeparableQuotient_iff_separable_evaluation :
    HasSeparableQuotient 𝕜 X ↔
    ∃ F : Submodule 𝕜 (StrongDual 𝕜 X), IsClosed (F : Set (StrongDual 𝕜 X)) ∧
      (¬ FiniteDimensional 𝕜 F) ∧
      TopologicalSpace.IsSeparable (Set.range (subspaceEvaluation F)) := by
  refine ⟨separable_evaluation_of_hasSeparableQuotient, ?_⟩
  rintro ⟨F, hFc, hFi, hsep⟩
  let := hFc
  exact hasSeparableQuotient_of_separable_evaluation F hFi hsep
end SeparableQuotient

end OAI
