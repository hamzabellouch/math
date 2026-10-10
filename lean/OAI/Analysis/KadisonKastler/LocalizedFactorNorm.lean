import OAI.Analysis.KadisonKastler.MinimalFamilyQuantity
import OAI.Analysis.KadisonKastler.CyclicFactorContinuity

namespace OAI

/-! The norm of a right factor localized by an operator in the original
commutant is constant on a minimal row family. -/

namespace KadisonKastler

noncomputable section

open scoped InnerProductSpace

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M : VonNeumannAlgebra H} {c : ℝ}

omit [CompleteSpace H] in
theorem isClosed_weakRectangularBall (a : ℝ) :
    IsClosed (weakRectangularBall H K a) := by
  by_cases ha : 0 ≤ a
  · exact (isCompact_weakRectangularBall ha).isClosed
  · have he : weakRectangularBall H K a = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro T hT
      exact ha ((norm_nonneg T.toCLM).trans hT)
    rw [he]
    exact isClosed_empty

omit [CompleteSpace H] in
theorem isClosed_localized_factor_norm {X : Type*} [TopologicalSpace X]
    (R : X → H →L[ℂ] K) (hR : Continuous (fun x => ContinuousLinearMapWOT.ofCLM (R x)))
    (T : H →L[ℂ] H) (a : ℝ) : IsClosed {x | ‖(R x).comp T‖ ≤ a} := by
  have hc : Continuous (fun x => ContinuousLinearMapWOT.ofCLM ((R x).comp T)) := by
    apply ContinuousLinearMapWOT.continuous_iff.mpr
    intro ξ η
    exact ContinuousLinearMapWOT.continuous_inner_apply hR (T ξ) η
  exact (isClosed_weakRectangularBall (H := H) (K := K) a).preimage hc

theorem representationRowAverage_comp_commutant
    (π : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K)) (R : H →L[ℂ] K)
    (T : H →L[ℂ] H)
    (hT : ∀ a : Algebra M, (a : H →L[ℂ] H).comp T = T.comp (a : H →L[ℂ] H))
    {ι : Type*} [Fintype ι] (r : ι → Algebra M) :
    (representationRowAverage π r R).comp T = representationRowAverage π r (R.comp T) := by
  ext ξ
  simp only [representationRowAverage, sum_apply, ContinuousLinearMap.comp_apply]
  apply Finset.sum_congr rfl
  intro i _
  have hi := congrArg (fun A : H →L[ℂ] H => A ξ) (hT (star (r i)))
  change (star (r i) : H →L[ℂ] H) (T ξ) = T ((star (r i) : H →L[ℂ] H) ξ) at hi
  rw [hi]

theorem minimal_row_family_localized_factor_norm
    (hc : 0 ≤ c) (C : Set (BoundedWeakAlgebraMap M c)) (hclosed : IsClosed C)
    (hinv : RowInvariant hc C)
    (hmin : ∀ D : Set (BoundedWeakAlgebraMap M c), D ⊆ C → D.Nonempty → IsClosed D →
      RowInvariant hc D → D = C)
    (π : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K)) (R : C → H →L[ℂ] K)
    (hR : Continuous (fun F => ContinuousLinearMapWOT.ofCLM (R F)))
    (hrow : ∀ (n : ℕ) (r : Fin n → Algebra M) (hr : ∑ i, r i * star (r i) = 1) (F : C),
      R ⟨boundedWeakRowAverage hc r hr F.val, hinv n r hr F.property⟩ =
        representationRowAverage π r (R F))
    (T : H →L[ℂ] H)
    (hT : ∀ a : Algebra M, (a : H →L[ℂ] H).comp T = T.comp (a : H →L[ℂ] H))
    (F G : C) : ‖(R F).comp T‖ = ‖(R G).comp T‖ := by
  apply minimal_row_family_quantity_constant_on hc C hclosed hinv hmin
    (fun F => ‖(R F).comp T‖) (isClosed_localized_factor_norm R hR T) _ F G
  intro n r hr A
  rw [hrow, representationRowAverage_comp_commutant π (R A) T hT r]
  exact representationRowAverage_norm_le π r hr ((R A).comp T)

end

end KadisonKastler

end OAI
