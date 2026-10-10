import OAI.Analysis.KadisonKastler.NearInclusionRepresentationComparison
import OAI.Analysis.KadisonKastler.ConjugateFactor

namespace OAI

/-! # The comparison error after a small unitary change of representation -/

namespace KadisonKastler

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M N : VonNeumannAlgebra H} {P Q : VonNeumannAlgebra K}

theorem conjugated_representation_comparison
    (e : Algebra M ≃⋆ₐ[ℂ] Algebra P) (f : Algebra N ≃⋆ₐ[ℂ] Algebra Q)
    {C D : ℝ}
    (hcomp : ∀ (a : Algebra M) (b : Algebra N), ‖a‖ ≤ 1 → ‖b‖ ≤ 1 →
      ‖(e a).val - (f b).val‖ ≤ C + ‖a.val - b.val‖)
    (w : unitary (K →L[ℂ] K)) (hw : ‖(w : K →L[ℂ] K) - 1‖ ≤ D)
    (a : Algebra M) (b : Algebra N) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ‖(e a).val - ((f.trans (unitaryConjugateEquiv (star w) Q)) b).val‖ ≤
      (C + 2 * D) + ‖a.val - b.val‖ := by
  have hf : ‖(f b).val‖ ≤ 1 := (NonUnitalStarAlgHom.norm_apply_le f b).trans hb
  have hs : ‖((star w : unitary (K →L[ℂ] K)) : K →L[ℂ] K) - 1‖ =
      ‖(w : K →L[ℂ] K) - 1‖ := by
    simpa only [Unitary.coe_star, star_sub, star_one] using norm_star ((w : K →L[ℂ] K) - 1)
  have hm := norm_unitaryConj_sub_le (star w) (f b).val
  rw [hs] at hm
  have hm' : ‖(f b).val - unitaryConj (star w) (f b).val‖ ≤ 2 * D := by
    rw [norm_sub_rev]
    exact hm.trans (by nlinarith [norm_nonneg ((w : K →L[ℂ] K) - 1)])
  exact (norm_sub_le_norm_sub_add_norm_sub (e a).val (f b).val
    (unitaryConj (star w) (f b).val)).trans (by linarith [hcomp a b ha hb])

end

end KadisonKastler

end OAI
