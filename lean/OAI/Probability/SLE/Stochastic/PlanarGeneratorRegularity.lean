import OAI.Probability.SLE.Geometry.CompactPlanarGaussian

namespace OAI

/-! Compact smooth tests retain bounded smoothness and Lipschitz control
under the planar Brownian generator. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

lemma planarGenerator_partial_formula
    (f : ℝ×ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    planarGenerator f = fun z => (1/2:ℝ)*
      (spatialPartial (f ∘ Prod.swap) 2 z.swap+spatialPartial f 2 z) := by
  funext z
  have hg : ContDiff ℝ (⊤ : ℕ∞) (f ∘ Prod.swap) :=
    hf.comp (contDiff_snd.prodMk contDiff_fst)
  rcases z with ⟨a,b⟩
  rw [spatialPartial_eq_iteratedDeriv _ hg,spatialPartial_eq_iteratedDeriv _ hf]
  rfl

lemma planarGenerator_smooth
    (f : ℝ×ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (planarGenerator f) := by
  rw [planarGenerator_partial_formula f hf]
  have hg : ContDiff ℝ (⊤ : ℕ∞) (f ∘ Prod.swap) :=
    hf.comp (contDiff_snd.prodMk contDiff_fst)
  exact contDiff_const.mul
    (((spatialPartial_smooth _ hg 2).comp (contDiff_snd.prodMk contDiff_fst)).add
      (spatialPartial_smooth f hf 2))

lemma planarGenerator_compact
    (f : ℝ×ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    HasCompactSupport (planarGenerator f) := by
  rw [planarGenerator_partial_formula f hf]
  have hg : HasCompactSupport (f ∘ Prod.swap) := hc.comp_homeomorph (Homeomorph.prodComm ℝ ℝ)
  have hh := (spatialPartial_compact _ hg 2).comp_homeomorph (Homeomorph.prodComm ℝ ℝ)
  exact (hh.add (spatialPartial_compact f hc 2)).mul_left

lemma planarGenerator_bounded_lipschitz
    (f : ℝ×ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    ∃ C : ℝ≥0, (∀ z, |planarGenerator f z|≤C) ∧ LipschitzWith C (planarGenerator f) := by
  simpa only [Real.norm_eq_abs] using compact_smooth_bounded_lipschitz (planarGenerator f)
    (planarGenerator_smooth f hf) (planarGenerator_compact f hf hc)

end SLEExactGauge

end

end OAI
