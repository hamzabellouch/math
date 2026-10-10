import OAI.Analysis.KadisonKastler.ConjugateHilbertProjection

namespace OAI

/-! # Normalizing a nonzero symmetric central line -/

namespace KadisonKastler

open Generator

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem exists_unit_symmetric_line (K : Submodule ℂ H)
    (J : H ≃ₗᵢ⋆[ℂ] H) (ξ : H) (hne : ξ ≠ 0)
    (hJξ : J ξ = ξ) (hξ : ξ ∈ K) (hline : K ≤ Submodule.span ℂ {ξ}) :
    ∃ η : H, ‖η‖ = 1 ∧ J η = η ∧ η ∈ K ∧ K ≤ Submodule.span ℂ {η} := by
  let c : ℂ := ((‖ξ‖⁻¹ : ℝ) : ℂ)
  let η := c • ξ
  have hn : 0 < ‖ξ‖ := norm_pos_iff.mpr hne
  have hc : c ≠ 0 := by
    change ((‖ξ‖⁻¹ : ℝ) : ℂ) ≠ 0
    exact_mod_cast (ne_of_gt (inv_pos.mpr hn))
  have hη : ‖η‖ = 1 := by
    dsimp [η,c]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn),
      inv_mul_cancel₀ hn.ne']
  refine ⟨η,hη,?_,K.smul_mem c hξ,?_⟩
  · change J (c • ξ) = c • ξ
    rw [J.map_smulₛₗ,hJξ]
    change star c • ξ = c • ξ
    have hcstar : star c = c := Complex.conj_ofReal _
    rw [hcstar]
  · apply le_trans hline
    apply Submodule.span_le.mpr
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    have he : ξ = c⁻¹ • η := by
      dsimp [η]
      rw [smul_smul,inv_mul_cancel₀ hc,one_smul]
    rw [he]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

end

end KadisonKastler

end OAI
