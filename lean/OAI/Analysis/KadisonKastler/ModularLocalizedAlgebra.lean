import OAI.Analysis.KadisonKastler.ModularLocalizedGraph
import OAI.Analysis.KadisonKastler.PositiveGraphAlgebraicApproximation

namespace OAI

/-! # Algebra elements approximating a short modular spectral vector -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {Ω : H}

theorem modular_localized_algebra_approximate
    (J : H ≃ₗᵢ⋆[ℂ] H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω))
    (d : ModularConjugationData M Ω)
    (hd : d.conjugation=tomitaPolarConjugation J Ω hsep hcyc)
    (ξ : H) {r δ : ℝ} (hδ : 0 ≤ δ)
    (hlo : modularUpperCut M J Ω r ξ=ξ)
    (hhi : modularUpperCut M J Ω (r+δ) ξ=0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (a : Algebra M) (q : ℝ), 0 < q ∧
      ‖a.val Ω-ξ‖ < (Real.exp δ-1)*‖ξ‖+ε ∧
      ‖((q : ℂ)⁻¹) • d.rightAction a Ω-ξ‖ < (Real.exp δ-1)*‖ξ‖+ε := by
  obtain ⟨x,y,q,hq,hgraph,hx,hy⟩ :=
    modular_localized_graph_pair J Ω hsep hcyc ξ hδ hlo hhi
  let tol := min ε (q*ε)
  have htol : 0 < tol := lt_min hε (mul_pos hq hε)
  obtain ⟨a,ha,hb⟩ := positiveGraph_algebraic_approximate J hsep hcyc d hd hgraph htol
  have hscaled : ‖((q : ℂ)⁻¹) • d.rightAction a Ω-y‖ < ε := by
    have hqne : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
    have he : ((q : ℂ)⁻¹) • d.rightAction a Ω-y =
        ((q : ℂ)⁻¹) • (d.rightAction a Ω-(q : ℂ) • y) := by
      rw [smul_sub,smul_smul,inv_mul_cancel₀ hqne,one_smul]
    rw [he,norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hq]
    calc
      _ < q⁻¹*tol := mul_lt_mul_of_pos_left hb (inv_pos.mpr hq)
      _ ≤ q⁻¹*(q*ε) := mul_le_mul_of_nonneg_left (min_le_right _ _) (inv_nonneg.mpr hq.le)
      _ = ε := by rw [← mul_assoc,inv_mul_cancel₀ hq.ne',one_mul]
  refine ⟨a,q,hq,?_,?_⟩
  · calc
      ‖a.val Ω-ξ‖ ≤ ‖a.val Ω-x‖+‖x-ξ‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < ε+(Real.exp δ-1)*‖ξ‖ :=
        add_lt_add_of_lt_of_le (ha.trans_le (min_le_left _ _)) hx
      _ = _ := add_comm _ _
  · calc
      ‖((q : ℂ)⁻¹) • d.rightAction a Ω-ξ‖ ≤
          ‖((q : ℂ)⁻¹) • d.rightAction a Ω-y‖+‖y-ξ‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < ε+(Real.exp δ-1)*‖ξ‖ := add_lt_add_of_lt_of_le hscaled hy
      _ = _ := add_comm _ _

end

end KadisonKastler

end OAI
