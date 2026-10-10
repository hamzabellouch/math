import Mathlib

namespace OAI

section
section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace WeakMTWTransport
section LocalJacobianBarrier
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

lemma abs_det_le_of_small_image_bounds {f : E → E} {A : E →L[ℝ] E} {x : E}
    (hf : HasStrictFDerivAt f A x) {C : ℝ} (hC : 0 ≤ C)
    (hsmall : ∀ U∈𝓝 x, ∃ s : Set E, s⊆U ∧ μ s≠0 ∧ μ s≠⊤ ∧
      μ (f '' s) ≤ ENNReal.ofReal C*μ s) : |A.det| ≤ C := by
  by_contra hbound
  have hbound : C < |A.det| := lt_of_not_ge hbound
  let m : ℝ≥0 := ⟨(C+|A.det|)/2,by positivity⟩
  have hmlo : C < (m:ℝ) := by change C < (C+|A.det|)/2; linarith only [hbound]
  have hmhi : (m:ℝ) < |A.det| := by change (C+|A.det|)/2 < |A.det|; linarith only [hbound]
  have hm : (m:ℝ≥0∞) < ENNReal.ofReal |A.det| := by
    rw [←ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_lt_ofReal_iff (hC.trans_lt hbound) |>.mpr hmhi
  have hpos : ∀ᶠ δ : ℝ≥0 in 𝓝[>] (0 : ℝ≥0), 0 < δ := self_mem_nhdsWithin
  obtain ⟨δ,hδ,Hδ⟩ := (hpos.and (mul_le_addHaar_image_of_lt_det μ A hm)).exists
  obtain ⟨U,hU,happrox⟩ := hf.approximates_deriv_on_nhds (Or.inr hδ)
  obtain ⟨s,hs,hs0,hsfin,hsimage⟩ := hsmall U hU
  have H := (Hδ s f (happrox.mono_set hs)).trans hsimage
  have Hm : (m:ℝ≥0∞) ≤ ENNReal.ofReal C :=
    (ENNReal.mul_le_mul_iff_left hs0 hsfin).mp H
  rw [←ENNReal.ofReal_coe_nnreal] at Hm
  have Hm' : (m:ℝ) ≤ C := (ENNReal.ofReal_le_ofReal_iff hC).mp Hm
  exact (not_le_of_gt hmlo) Hm'

end LocalJacobianBarrier
end WeakMTWTransport

end

end

end

end OAI
