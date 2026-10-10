import OAI.Probability.BenjaminiSchramm.PeakSlabComparison

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

def fullPeakDownProbability (O : G.OrbitRepresentatives) (a : V → ℝ)
    (p : unitInterval) (ell : ℝ) : ℝ≥0∞ :=
  ∑ x ∈ O.roots, ENNReal.ofReal (a x)*G.law p (G.fullPeakDownHit a ell x)

theorem weighted_full_peak_lower_slab_comparison
    (O : G.OrbitRepresentatives) (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (a : V → ℝ)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x)
    (d N : ℕ) (hd : ∀ z, Percolation.degree G.ends z ≤ d)
    (p : unitInterval) (R M k r ell : ℝ) (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hk : 0 ≤ k) (hr : 0 ≤ r) (hell : 0 < ell)
    (hjump : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e → |G.orbitAdjustedHeight a v w| ≤ R)
    (hpaths : ∀ u (j : G.VertexOrbit), ∃ v, ∃ q : G.fullGraph.Walk u v,
      G.vertexOrbit v=j ∧ q.length ≤ N ∧
      (∀ z ∈ q.support, -M ≤ G.orbitAdjustedHeight a u z ∧ G.orbitAdjustedHeight a u z ≤ 0) ∧
      G.orbitAdjustedHeight a u v ≤ -R)
    (hfin : ∀ v, ∀ᵐ ω ∂G.law p, (Percolation.cluster G.ends ω v).Finite) (v₀ : V) :
    G.fullPeakDownProbability O a p ell*
      ENNReal.ofReal ((min (p : ℝ) (1-p))^(d*(N+1)))*
        G.mixedHeightLayerMoment a p (-k-r) 0 (-k-R) (-k+R) (-k-r-2*M-2*R) ell v₀ ≤
      ∑ x ∈ O.roots, ENNReal.ofReal (a x)*
        (∫⁻ ω, G.strictPeakSlabBandCount a (r+R+M) (-ell-k-M-2*R) (-ell-k) ω x ∂G.law p) := by
  unfold fullPeakDownProbability
  rw [Finset.sum_mul,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro x _
  simpa only [mul_assoc] using mul_le_mul' (le_refl (ENNReal.ofReal (a x)))
    (G.full_peak_lower_slab_comparison hc hl a ha d N hd p R M k r ell hR hM hk hr hell
      hjump hpaths hfin x v₀)

end CriticalPercolation.BondGraph

end

end OAI
