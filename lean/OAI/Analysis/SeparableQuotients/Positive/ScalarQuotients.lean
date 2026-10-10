import OAI.Analysis.SeparableQuotients.Positive.ScalarEvaluation
import OAI.Analysis.SeparableQuotients.Positive.ScalarAdjoint
import OAI.Analysis.SeparableQuotients.Positive.DualSequences

namespace OAI

noncomputable section

section
open Set Metric Filter TopologicalSpace MeasureTheory Function
open scoped Classical BigOperators Topology Cardinal ENNReal NNReal

namespace SeparableQuotient.Positive.Fields.Scalar
universe u
attribute [local instance] dualSubmoduleNormedGroup dualSubmoduleNormedSpace
open Set TopologicalSpace
open scoped Classical
variable {𝕜 : Type} [RCLike 𝕜]
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]


theorem quotient_of_separable_evaluation
    (F : Submodule 𝕜 (StrongDual 𝕜 X)) (hF : IsClosed (F : Set (StrongDual 𝕜 X)))
    (hinf : ¬ FiniteDimensional 𝕜 F)
    (hsep : IsSeparable (Set.range (evaluation F))) : HasSeparableQuotient 𝕜 X := by
  classical
  let : SeparableSpace (Set.range (evaluation F)) := hsep.separableSpace
  let : Nonempty (Set.range (evaluation F)) := ⟨⟨evaluation F 0, Set.mem_range_self 0⟩⟩
  obtain ⟨y, hy⟩ := exists_dense_seq (α := Set.range (evaluation F))
  choose x hx using fun n => (y n).property
  have hdense : Set.range (evaluation F) ⊆ closure (Set.range (fun n => evaluation F (x n))) := by
    have hh := (Subtype.dense_iff.mp hy)
    have he : Subtype.val '' Set.range y = Set.range (fun n => evaluation F (x n)) := by
      ext z
      simp only [Set.mem_image, Set.mem_range]
      constructor
      · rintro ⟨w, ⟨n, rfl⟩, rfl⟩; exact ⟨n, hx n⟩
      · rintro ⟨n, rfl⟩; exact ⟨y n, ⟨n, rfl⟩, (hx n).symm⟩
    rw [he] at hh
    exact hh
  obtain ⟨g, D, hg, hD, hn, hann, htest⟩ := exists_normed_prefix_sequence F hinf x
  let f : ℕ → StrongDual 𝕜 X := fun n => g n
  have hf (n : ℕ) : (1:ℝ) ≤ ‖f n‖ := (hg n).ge
  have hn' m (v : StrongDual 𝕜 X)
      (hv : v ∈ Submodule.span 𝕜 (f '' (Finset.range m : Set ℕ))) :
      ∃ d ∈ D m, ‖v‖ ≤ 2 * ‖v d‖ := by
    exact hn m v hv
  have hp := prefixBound_of_half_normers 𝕜 f D hD hn' hann
  have hs : ∀ z ∈ Set.range (fun n => evaluation F (x n)),
      Summable (fun n => ‖z (g n)‖) := by
    rintro z ⟨j, rfl⟩
    apply summable_of_ne_finset_zero (s := Finset.range j)
    intro n hn
    have hnj : j ≤ n := by simpa only [Finset.mem_range, not_lt] using hn
    change ‖(g n : StrongDual 𝕜 X) (x j)‖ = 0
    rw [htest n j hnj, norm_zero]
  have hrange := eval_range_of_dense_summable F hF g hp (by norm_num : (0:ℝ) < 1) hf
    (Set.range (fun n => evaluation F (x n)))
    (fun z hz => hdense (by obtain ⟨w, _, rfl⟩ := hz; exact Set.mem_range_self w)) hs
  obtain ⟨hsurj, hZsep, hZinf⟩ :=
    prefix_evaluation_surjective f (by norm_num : (0:ℝ) < 1) hf D hD hn' hann hrange
  refine ⟨ClosedSpan 𝕜 (prefixCoord 𝕜 f), inferInstance, inferInstance, inferInstance, hZsep, hZinf, ?_⟩
  exact ⟨(evaluation (ClosedSpan 𝕜 f)).codRestrict (ClosedSpan 𝕜 (prefixCoord 𝕜 f)) hrange, hsurj⟩
end SeparableQuotient.Positive.Fields.Scalar

end

section
open Set Metric Filter TopologicalSpace MeasureTheory Function
open scoped Classical BigOperators Topology Cardinal ENNReal NNReal

namespace SeparableQuotient.Positive.Fields
variable {𝕜 : Type*} [RCLike 𝕜] {V : Type*}
    [NormedAddCommGroup V] [NormedSpace 𝕜 V]



theorem exists_separable_closed_infinite_subspace (hV : ¬ FiniteDimensional 𝕜 V) :
    ∃ F : Submodule 𝕜 V, IsClosed (F : Set V) ∧ SeparableSpace F ∧
      ¬ FiniteDimensional 𝕜 F := by
  classical
  let B := Module.Free.chooseBasis 𝕜 V
  let : Infinite (Module.Free.ChooseBasisIndex 𝕜 V) := ⟨by
    intro h
    let := h
    exact hV B.finiteDimensional_of_finite⟩
  let e := Infinite.natEmbedding (Module.Free.ChooseBasisIndex 𝕜 V)
  let f : ℕ → V := B ∘ e
  have hf : LinearIndependent 𝕜 f := B.linearIndependent.comp e e.injective
  let F : Submodule 𝕜 V := (Submodule.span 𝕜 (Set.range f)).topologicalClosure
  refine ⟨F, Submodule.isClosed_topologicalClosure _, ?_, ?_⟩
  · exact ((Set.countable_range f).isSeparable.span (R := 𝕜)).closure.separableSpace
  · intro hfd
    let := hfd
    let g (n : ℕ) : F := ⟨f n, Submodule.le_topologicalClosure _
      (Submodule.subset_span (Set.mem_range_self n))⟩
    have hg : LinearIndependent 𝕜 g := hf.of_comp F.subtype
    have hh := hg.lt_aleph0_of_finiteDimensional
    simp at hh



theorem infiniteDimensional_strongDual (hV : ¬ FiniteDimensional 𝕜 V) :
    ¬ FiniteDimensional 𝕜 (StrongDual 𝕜 V) := by
  intro h
  let := h
  let J : V →ₗ[𝕜] StrongDual 𝕜 (StrongDual 𝕜 V) :=
    (NormedSpace.inclusionInDoubleDualLi 𝕜 (E := V)).toLinearMap
  have hJ : Function.Injective J := by
    intro x y hxy
    exact (NormedSpace.inclusionInDoubleDualLi 𝕜 (E := V)).injective hxy
  apply hV
  exact FiniteDimensional.of_injective (V₂ := StrongDual 𝕜 (StrongDual 𝕜 V)) J hJ
end SeparableQuotient.Positive.Fields

end

section
open Set Metric Filter TopologicalSpace MeasureTheory Function
open scoped Classical BigOperators Topology Cardinal ENNReal NNReal

namespace SeparableQuotient.Positive.Fields.Scalar
attribute [local instance] dualSubmoduleNormedGroup dualSubmoduleNormedSpace
open Set TopologicalSpace
variable {𝕜 : Type} [RCLike 𝕜]
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]

lemma dual_lower_of_surjective (T : X →L[𝕜] Y) (hsurj : Function.Surjective T) :
    ∃ C : NNReal, ∀ g : StrongDual 𝕜 Y, ‖g‖ ≤ C * ‖g.comp T‖ := by
  obtain ⟨C, hC, hpre⟩ := T.exists_preimage_norm_le hsurj
  refine ⟨⟨C, hC.le⟩, fun g => g.opNorm_le_bound (by positivity) ?_⟩
  intro y
  obtain ⟨x, hx, hnorm⟩ := hpre y
  calc
    ‖g y‖ = ‖(g.comp T) x‖ := by rw [ContinuousLinearMap.comp_apply, hx]
    _ ≤ ‖g.comp T‖ * ‖x‖ := (g.comp T).le_opNorm x
    _ ≤ ‖g.comp T‖ * (C * ‖y‖) := mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
    _ = (C * ‖g.comp T‖) * ‖y‖ := by ring



theorem separable_evaluation_of_quotient [SeparableSpace Y]
    (T : X →L[𝕜] Y) (hsurj : Function.Surjective T)
    (hY : ¬ FiniteDimensional 𝕜 Y) :
    ∃ F : Submodule 𝕜 (StrongDual 𝕜 X),
      IsClosed (F : Set (StrongDual 𝕜 X)) ∧ SeparableSpace F ∧
        ¬ FiniteDimensional 𝕜 F ∧ IsSeparable (Set.range (evaluation F)) := by
  obtain ⟨U, hUclosed, hUsep, hUinf⟩ := exists_separable_closed_infinite_subspace
    (infiniteDimensional_strongDual hY)
  let := hUsep
  let : IsClosed (U : Set (StrongDual 𝕜 Y)) := hUclosed
  let A : StrongDual 𝕜 Y →L[𝕜] StrongDual 𝕜 X := T.precomp 𝕜
  let B : U →L[𝕜] StrongDual 𝕜 X := A.comp U.subtypeL
  obtain ⟨C, hC⟩ := dual_lower_of_surjective T hsurj
  have hB : AntilipschitzWith C B := B.antilipschitz_of_bound (fun u => hC u)
  have hBclosed : IsClosed (Set.range B) := (hB.isClosedEmbedding B.uniformContinuous).isClosed_range
  let F : Submodule 𝕜 (StrongDual 𝕜 X) := B.toLinearMap.range
  let e : U ≃L[𝕜] F := ContinuousLinearMap.equivRange hB.injective hBclosed
  have hFsep : SeparableSpace F := e.surjective.denseRange.separableSpace e.continuous
  have hFinf : ¬ FiniteDimensional 𝕜 F := by
    intro hh
    let := hh
    exact hUinf e.symm.toLinearEquiv.finiteDimensional
  let J : F →L[𝕜] U := e.symm.toContinuousLinearMap
  let S : Y →L[𝕜] StrongDual 𝕜 F := (J.precomp 𝕜).comp (evaluation U)
  have hST (x : X) : S (T x) = evaluation F x := by
    ext f
    have he : B (e.symm f) = (f : StrongDual 𝕜 X) :=
      congrArg Subtype.val (e.apply_symm_apply f)
    exact congrArg (fun g : StrongDual 𝕜 X => g x) he
  refine ⟨F, hBclosed, hFsep, hFinf, ?_⟩
  apply (isSeparable_range S.continuous).mono
  rintro z ⟨x, rfl⟩
  exact ⟨T x, hST x⟩


theorem evaluation_criterion : HasSeparableQuotient 𝕜 X ↔
    ∃ F : Submodule 𝕜 (StrongDual 𝕜 X),
      IsClosed (F : Set (StrongDual 𝕜 X)) ∧
        ¬ FiniteDimensional 𝕜 F ∧ IsSeparable (Set.range (evaluation F)) := by
  constructor
  · rintro ⟨Y, ng, ns, hcomplete, hsep, hinf, T, hT⟩
    let := ng
    let := ns
    let := hcomplete
    let := hsep
    obtain ⟨F, hFcl, _, hFinf, hFeval⟩ := separable_evaluation_of_quotient T hT hinf
    exact ⟨F, hFcl, hFinf, hFeval⟩
  · rintro ⟨F, hFcl, hFinf, hFeval⟩
    exact quotient_of_separable_evaluation F hFcl hFinf hFeval
end SeparableQuotient.Positive.Fields.Scalar

end

end

end OAI
