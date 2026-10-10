import OAI.Probability.SLE.Geometry.ReflectedInvertedUpperConnected
import OAI.Probability.SLE.Geometry.SymmetricChartUpperBijective

namespace OAI

/-! The reflected-slit Riemann map normalized at infinity, including its
exact upper-side image. This remains a static conformal chart. -/
noncomputable section
open Set Complex Metric Function
open scoped ComplexConjugate

namespace SLEExactGauge

theorem reflected_slit_exists_normalized_chart
    (p : C(unitInterval,ℂ)) (hi : Injective p) (h0 : p 0=0)
    (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane) :
    ∃ (f : ℂ → ℂ) (a : ℝ), 0 < a ∧
      BijOn f (invertedExterior (reflectedArcSet p)) (ball 0 1) ∧
      DifferentiableOn ℂ f (invertedExterior (reflectedArcSet p)) ∧
      f 0=0 ∧ deriv f 0=(a:ℂ) ∧
      (∀ z ∈ invertedExterior (reflectedArcSet p), f (conj z)=conj (f z)) ∧
      BijOn f (invertedExterior (reflectedArcSet p) ∩ upperHalfPlane)
        (ball 0 1 ∩ upperHalfPlane) := by
  have hK : IsCompact (reflectedArcSet p) := (isCompact_range p.continuous).union
    ((isCompact_range p.continuous).image Complex.continuous_conj)
  have ho := invertedExterior_isOpen hK
  have hz := zero_mem_invertedExterior (reflectedArcSet p)
  have hproper : invertedExterior (reflectedArcSet p) ≠ univ := by
    intro he
    have hp1 : p 1 ≠ 0 := by
      intro hp1
      have ht := hi (hp1.trans h0.symm)
      norm_num at ht
    have hm : (p 1)⁻¹ ∈ invertedExterior (reflectedArcSet p) := by rw [he]; trivial
    rcases hm with hm|hm
    · exact inv_ne_zero hp1 hm
    · apply hm
      rw [inv_inv]
      exact Or.inl (mem_range_self 1)
  obtain ⟨f,hb,hf,hf0,a,ha,hfa⟩ := exists_zero_normalized_riemann_chart ho
    (reflected_slit_inverted_simplyConnected p hi h0 hH) hproper hz
  have hD := invertedExterior_conj (reflectedArcSet_conj p)
  have hsym := normalized_riemann_chart_conj ho hz hD hf hb hf0 hfa
  have hupper := normalized_riemann_maps_upper ho hz hD
    (reflected_inverted_upper_connected p hi h0 hH).isPreconnected hf hb hf0 ha hfa
  exact ⟨f,a,ha,hb,hf,hf0,hfa,hsym,symmetric_disk_chart_upper_bijOn hD hb hsym hupper⟩

end SLEExactGauge

end

end OAI
