import OAI.Analysis.KadisonKastler.FullCornerEmbedding

namespace OAI

/-! # Putting countable matrix entries in common position -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {E : Submodule ℂ H} [CompleteSpace E]

namespace FullMatrixCorner

/-- The constructed finite-group embedding makes all countable matrix entries
common and retains the elementary displacement and gap estimates. -/
theorem exists_common_neighbor (F : FullMatrixCorner E) (M N : VonNeumannAlgebra H)
    (hF : ∀ i j, F.entry i j ∈ M) {γ : ℝ}
    (hsmall : γ ≤ 1 / 1152) (hgap : kkDistance M N < γ) :
    ∃ w : unitary (H →L[ℂ] H),
      ‖(w : H →L[ℂ] H) - 1‖ ≤ 150 * γ ∧
      (∀ i j, F.entry i j ∈ unitaryConjugateAlgebra (star w) N) ∧
      kkDistance M (unitaryConjugateAlgebra (star w) N) ≤
        kkDistance M N + 2 * ‖(w : H →L[ℂ] H) - 1‖ := by
  have hγ : 0 ≤ γ := ((kkDistance_nonneg M N).trans_lt hgap).le
  obtain ⟨w, _, hw, hn⟩ := F.exists_localized_embedding M N hF hγ hsmall
    (nearInclusion_of_kkDistance_lt hgap)
  refine ⟨w, by linarith, ?_, ?_⟩
  · intro i j
    exact ⟨unitaryConj w (F.entry i j), hw i j, unitaryConj_star_unitaryConj w _⟩
  · have hstar : ‖((star w : unitary (H →L[ℂ] H)) : H →L[ℂ] H) - 1‖ =
        ‖(w : H →L[ℂ] H) - 1‖ := by
      simpa only [Unitary.coe_star, star_sub, star_one] using
        norm_star ((w : H →L[ℂ] H) - 1)
    simpa only [hstar] using
      (kkDistance_conjugate_le (M := M) (conjugates_unitaryConjugateAlgebra (star w) N))

end FullMatrixCorner

end

end KadisonKastler

end OAI
