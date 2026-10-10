import OAI.GroupTheory.PolycyclicRecognition.Analysis.LipschitzProfileFTC

namespace OAI

/-! # Pairwise almost-everywhere derivative agreement makes profile lines affine -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set Filter
open scoped NNReal

theorem exists_affine_of_lipschitz_pairwise_derivative
    {W I : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (α : I → W →L[ℝ] ℝ) (hsep : ∀ w : W, (∀ i, α i w = 0) → w = 0)
    {h q : ℝ → W} {C : ℝ≥0} {T : ℝ} (hT : 0 ≤ T)
    (hlip : LipschitzOnWith C h (Icc 0 T))
    (hderiv : ∀ᵐ t ∂volume.restrict (Icc 0 T), HasDerivAt h (q t) t)
    (hpair : ∀ᵐ s ∂volume.restrict (Icc 0 T),
      ∀ᵐ t ∂volume.restrict (Icc 0 T), q s = q t) :
    ∃ u : W, ∀ t ∈ Icc 0 T, h t = h 0 + t • u := by
  let μ : Measure ℝ := volume.restrict (Icc 0 T)
  by_cases hμ : μ = 0
  · have hzero : ENNReal.ofReal T = 0 := by
      have hm := congrArg (fun ν : Measure ℝ => ν univ) hμ
      simpa [μ] using hm
    have hTzero : T = 0 := le_antisymm (ENNReal.ofReal_eq_zero.mp hzero) hT
    subst T
    refine ⟨0, ?_⟩
    intro t ht
    have htzero : t = 0 := le_antisymm ht.2 ht.1
    simp [htzero]
  · let : NeZero μ := ⟨hμ⟩
    obtain ⟨s, hs⟩ := (show ∀ᵐ s ∂μ, ∀ᵐ t ∂μ, q s = q t from hpair).exists
    refine ⟨q s, affine_of_lipschitz_ae_constant_derivative α hsep hT hlip (q s) ?_⟩
    filter_upwards [hderiv, hs] with t ht hst
    rwa [← hst] at ht

theorem exists_affine_mem_of_lipschitz_pairwise_derivative
    {W I : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (α : I → W →L[ℝ] ℝ) (hsep : ∀ w : W, (∀ i, α i w = 0) → w = 0)
    {h q : ℝ → W} {C : ℝ≥0} {T : ℝ} (hT : 0 < T)
    (hlip : LipschitzOnWith C h (Icc 0 T))
    (hderiv : ∀ᵐ t ∂volume.restrict (Icc 0 T), HasDerivAt h (q t) t)
    (hpair : ∀ᵐ s ∂volume.restrict (Icc 0 T),
      ∀ᵐ t ∂volume.restrict (Icc 0 T), q s = q t)
    {E : Set W} (hq : ∀ᵐ t ∂volume.restrict (Icc 0 T), q t ∈ E) :
    ∃ u ∈ E, ∀ t ∈ Icc 0 T, h t = h 0 + t • u := by
  let μ : Measure ℝ := volume.restrict (Icc 0 T)
  have hμ : μ ≠ 0 := by
    intro hz
    have hm := congrArg (fun ν : Measure ℝ => ν univ) hz
    have he : ENNReal.ofReal T = 0 := by simpa [μ] using hm
    exact (not_le_of_gt hT) (ENNReal.ofReal_eq_zero.mp he)
  let : NeZero μ := ⟨hμ⟩
  obtain ⟨s, hs, hsE⟩ := (hpair.and hq).exists
  refine ⟨q s, hsE, affine_of_lipschitz_ae_constant_derivative α hsep hT.le hlip (q s) ?_⟩
  filter_upwards [hderiv, hs] with t ht hst
  rwa [← hst] at ht

end PolycyclicRecognition

end

end OAI
