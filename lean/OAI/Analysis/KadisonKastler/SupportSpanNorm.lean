import OAI.Analysis.KadisonKastler.FiniteSupportRows

namespace OAI

/-! Uniform norm bounds on finite initial sums extend to the full central
support. The argument uses norm density, without normality of a representation. -/

namespace KadisonKastler

noncomputable section

open Generator Generator.Tracial

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [NormedSpace ℂ K]
  {M : VonNeumannAlgebra H}

theorem finiteSupportSum_fixes_of_subset (s t : Finset (PartialIsometry M))
    (ho : ∀ v ∈ t, ∀ w ∈ t, v ≠ w → v.support.val * w.support.val = 0)
    (hst : s ⊆ t) (ξ : H)
    (hξ : (finiteSupportSum s : H →L[ℂ] H) ξ = ξ) :
    (finiteSupportSum t : H →L[ℂ] H) ξ = ξ := by
  have h := congrArg (fun a : Algebra M => (a : H →L[ℂ] H) ξ)
    (finiteSupportSum_mul_of_subset s t ho hst)
  change (finiteSupportSum t : H →L[ℂ] H) ((finiteSupportSum s : H →L[ℂ] H) ξ) =
    (finiteSupportSum s : H →L[ℂ] H) ξ at h
  rwa [hξ] at h

theorem support_span_has_finite_support (S : Set (PartialIsometry M))
    (ho : S.Pairwise (fun v w => v.support.val * w.support.val = 0))
    {ξ : H} (hξ : ξ ∈ Submodule.span ℂ (partialSupportVectors S)) :
    ∃ s : Finset (PartialIsometry M), (↑s : Set (PartialIsometry M)) ⊆ S ∧
      (finiteSupportSum s : H →L[ℂ] H) ξ = ξ := by
  classical
  induction hξ using Submodule.span_induction with
  | mem ξ hξ =>
      obtain ⟨v, hv, η, rfl⟩ := hξ
      refine ⟨{v}, by simpa using hv, ?_⟩
      have h := congrArg (fun a : Algebra M => (a : H →L[ℂ] H) η)
        v.support.property.isIdempotentElem.eq
      simpa only [finiteSupportSum, Finset.sum_singleton, MulMemClass.coe_mul,
        mul_apply_eq_comp] using h
  | zero => exact ⟨∅, by simp, by simp [finiteSupportSum]⟩
  | add ξ η _ _ hξ hη =>
      obtain ⟨s, hs, hξ⟩ := hξ
      obtain ⟨t, ht, hη⟩ := hη
      have hu : (↑(s ∪ t) : Set (PartialIsometry M)) ⊆ S := by
        intro v hv
        rcases Finset.mem_union.mp hv with hv | hv
        · exact hs hv
        · exact ht hv
      have huo : ∀ v ∈ s ∪ t, ∀ w ∈ s ∪ t, v ≠ w →
          v.support.val * w.support.val = 0 := fun v hv w hw => ho (hu hv) (hu hw)
      refine ⟨s ∪ t, hu, ?_⟩
      rw [map_add, finiteSupportSum_fixes_of_subset s (s ∪ t) huo Finset.subset_union_left ξ hξ,
        finiteSupportSum_fixes_of_subset t (s ∪ t) huo Finset.subset_union_right η hη]
  | smul z ξ _ hξ =>
      obtain ⟨s, hs, hξ⟩ := hξ
      exact ⟨s, hs, by rw [map_smul, hξ]⟩

theorem norm_comp_partialSupportProjection_le (S : Set (PartialIsometry M))
    (ho : S.Pairwise (fun v w => v.support.val * w.support.val = 0))
    (A : H →L[ℂ] K) {d : ℝ} (hd : 0 ≤ d)
    (hA : ∀ s : Finset (PartialIsometry M), (↑s : Set (PartialIsometry M)) ⊆ S →
      ‖A.comp (finiteSupportSum s : H →L[ℂ] H)‖ ≤ d) :
    ‖A.comp ((partialSupportProjection S).val : H →L[ℂ] H)‖ ≤ d := by
  have hb : ∀ ξ ∈ partialSupportSpace S, ‖A ξ‖ ≤ d * ‖ξ‖ := by
    intro ξ hξ
    have hs : (Submodule.span ℂ (partialSupportVectors S) : Set H) ⊆
        {η | ‖A η‖ ≤ d * ‖η‖} := by
      intro η hη
      obtain ⟨s, hs, he⟩ := support_span_has_finite_support S ho hη
      change ‖A η‖ ≤ d * ‖η‖
      have h := (A.comp (finiteSupportSum s : H →L[ℂ] H)).le_of_opNorm_le (hA s hs) η
      simpa only [ContinuousLinearMap.comp_apply, he] using h
    have hc : IsClosed {η : H | ‖A η‖ ≤ d * ‖η‖} :=
      isClosed_le (A.continuous.norm) (continuous_const.mul continuous_norm)
    exact closure_minimal hs hc hξ
  apply ContinuousLinearMap.opNorm_le_bound _ hd
  intro ξ
  have h := hb _ ((partialSupportSpace S).starProjection_apply_mem ξ)
  have hp := ((partialSupportProjection S).property.map M.toStarSubalgebra.subtype).norm_le
  have hpξ := (((partialSupportProjection S).val : H →L[ℂ] H).le_of_opNorm_le hp ξ)
  change ‖(partialSupportSpace S).starProjection ξ‖ ≤ 1 * ‖ξ‖ at hpξ
  rw [one_mul] at hpξ
  exact h.trans (mul_le_mul_of_nonneg_left hpξ hd)

end

end KadisonKastler

end OAI
