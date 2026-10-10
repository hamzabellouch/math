import OAI.Combinatorics.Progressions.Probability.PrincipalMixedMassBound

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem frozen_mixed_pmf_comparison {Z : Type*} [Fintype Z]
    {X R V W : Z → Type*} [∀ z, Fintype (X z)] [∀ z, DecidableEq (X z)]
    [∀ z, Fintype (R z)] [∀ z, DecidableEq (R z)]
    (outer : FiniteProbabilityWeights Z) (p : ∀ z, FiniteProbabilityWeights (X z))
    (label : ∀ z, X z → R z) (tv : ∀ z, Finset (V z)) (tw : ∀ z, Finset (W z))
    (coefficient : ∀ z, X z → PMF (W z)) (scale : Z → ℝ)
    (target : ∀ z, R z → W z → ℝ) (a : ∀ z, X z → V z → ℂ)
    (b : ∀ z, R z → V z → ℂ) (φ : ∀ z, V z × W z → ℂ)
    {δ ε S : ℝ} (hδ : 0 ≤ δ) (hε : 0 ≤ ε) (hS : 0 ≤ S)
    (hscale : ∀ z, outer.weight z ≠ 0 → 0 ≤ scale z)
    (hcard : ∀ z, outer.weight z ≠ 0 → scale z ≤ (tw z).card)
    (hφ : ∀ z, outer.weight z ≠ 0 → ∀ v ∈ tv z ×ˢ tw z, ‖φ z v‖ ≤ 1)
    (hspatial : ∀ z, outer.weight z ≠ 0 → ∀ x, (p z).weight x ≠ 0 →
      ∀ v ∈ tv z, ‖a z x v-b z (label z x) v‖ ≤ δ)
    (hcoeff : ∀ z, outer.weight z ≠ 0 → ∀ r
      (hr : 0 < (p z).mass (Finset.univ.filter (fun x => label z x = r))), ∀ w ∈ tw z,
        |((p z).condition _ hr).mean (fun x => scale z*(coefficient z x w).toReal)-target z r w| ≤ ε)
    (hsite : ∀ z, outer.weight z ≠ 0 → ∀ r v, v ∈ tv z → ‖b z r v‖ ≤ S) :
    ‖outer.complexMean (fun z => (p z).complexMean (fun x => 𝔼 v ∈ tv z ×ˢ tw z,
        ((scale z*(coefficient z x v.2).toReal : ℝ) : ℂ)*a z x v.1*φ z v)) -
      outer.complexMean (fun z => ∑ r, 𝔼 v ∈ tv z ×ˢ tw z,
        ((((p z).fiberLaw (label z)).weight r*target z r v.2 : ℝ) : ℂ)*b z r v.1*φ z v)‖ ≤ δ+ε*S := by
  have hc : ∀ z, outer.weight z ≠ 0 → ∀ x, (p z).weight x ≠ 0 →
      ∀ v ∈ tv z ×ˢ tw z, 0 ≤ scale z*(coefficient z x v.2).toReal := by
    intro z hz x _ v _
    exact mul_nonneg (hscale z hz) ENNReal.toReal_nonneg
  have hsp : ∀ z, outer.weight z ≠ 0 → ∀ x, (p z).weight x ≠ 0 →
      ∀ v ∈ tv z ×ˢ tw z, ‖a z x v.1-b z (label z x) v.1‖ ≤ δ := by
    intro z hz x hx v hv
    exact hspatial z hz x hx v.1 (Finset.mem_product.mp hv).1
  have hcf : ∀ z, outer.weight z ≠ 0 → ∀ r v, v ∈ tv z ×ˢ tw z →
      |(p z).fiberMean (label z) r (fun x => scale z*(coefficient z x v.2).toReal)-
        ((p z).fiberLaw (label z)).weight r*target z r v.2| ≤ ((p z).fiberLaw (label z)).weight r*ε := by
    intro z hz r v hv
    apply FiniteProbabilityWeights.fiberMean_condition_error
    intro hr
    exact hcoeff z hz r hr v.2 (Finset.mem_product.mp hv).2
  have hC : ∀ z, outer.weight z ≠ 0 →
      (p z).mean (fun x => 𝔼 v ∈ tv z ×ˢ tw z, scale z*(coefficient z x v.2).toReal) ≤ 1 := by
    intro z hz
    exact scaledPMF_product_mean_le_one (p z) (coefficient z) (tv z) (tw z) (hscale z hz) (hcard z hz)
  have hB : ∀ z, outer.weight z ≠ 0 →
      ((p z).fiberLaw (label z)).mean (fun r => 𝔼 v ∈ tv z ×ˢ tw z, ‖b z r v.1‖) ≤ S := by
    intro z hz
    apply finiteMean_le_of_support
    intro r _
    apply finite_expect_le_of_nonneg_bound _ _ hS
    intro v hv
    exact hsite z hz r v.1 (Finset.mem_product.mp hv).1
  have he := frozen_mixed_residue_comparison_of_mass outer p label (fun z => tv z ×ˢ tw z)
    (fun z x v => scale z*(coefficient z x v.2).toReal) (fun z r v => target z r v.2)
    (fun z x v => a z x v.1) (fun z r v => b z r v.1) φ hδ hε hc hφ hsp hcf hC hB
  simpa only [mul_one] using he

end Erdos3

end

end OAI
