import OAI.Probability.BenjaminiSchramm.CeilingBandTransport
import OAI.Probability.BenjaminiSchramm.LayerFirstMoments
import OAI.Probability.BenjaminiSchramm.IntegerLayerFirstVisit

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

lemma restrictedLayerCount_expectation_le_row_bound (p : unitInterval)
    (C : ℝ≥0∞) (hrow : ∀ z, (∑' y, law p {ω | Conn G ω z y}) ≤ C)
    (I : Set E) (A : Set V) (x : V) :
    (∫⁻ ω, restrictedLayerCount G I A ω x ∂law p) ≤ C := by
  rw [lintegral_restrictedLayerCount]
  apply le_trans _ (hrow x)
  apply ENNReal.tsum_le_tsum
  intro y
  split_ifs
  · exact measure_mono fun ω hω => conn_mono G Set.inter_subset_left hω
  · exact bot_le

theorem first_layer_moment_bound_with_row (p : unitInterval)
    (C : ℝ≥0∞) (hrow : ∀ z, (∑' y, law p {ω | Conn G ω z y}) ≤ C)
    (f : V → ℤ) (hjump : ∀ e v w, v ∈ G e → w ∈ G e →
      f w ≤ f v+1 ∧ f v ≤ f w+1)
    (I : Set E) (A : Set V) (x : V) (n : ℤ)
    (hx : f x < n) (hA : ∀ y ∈ A, n ≤ f y) :
    (∫⁻ ω, restrictedLayerCount G I A ω x ∂law p) ≤
      (∫⁻ ω, restrictedLayerCount G (internalEdges G {v | f v ≤ n})
        {v | f v=n} ω x ∂law p)*C := by
  have hfirst := integer_first_layer_moment_bound G f hjump I A p x n hx hA
  have hprefix (z : V) :
      law p {ω | Conn G (ω ∩ (I ∩ internalEdges G {v | f v ≤ n})) x z} ≤
      law p {ω | Conn G (ω ∩ internalEdges G {v | f v ≤ n}) x z} :=
    measure_mono (fun ω hω => conn_mono G
      (Set.inter_subset_inter_right _ Set.inter_subset_right) hω)
  calc
    _ ≤ ∑' z, (if f z=n then
        law p {ω | Conn G (ω ∩ internalEdges G {v | f v ≤ n}) x z} else 0)*C := by
      apply hfirst.trans
      apply ENNReal.tsum_le_tsum
      intro z
      by_cases hz : f z=n
      · simp only [ite_eq_left hz]
        exact mul_le_mul' (hprefix z)
          (restrictedLayerCount_expectation_le_row_bound G p C hrow I A z)
      · simp only [ite_eq_right hz,zero_mul,le_refl]
    _ = _ := by
      rw [ENNReal.tsum_mul_right]
      congr 1
      rw [lintegral_restrictedLayerCount]
      apply tsum_congr
      intro z
      by_cases hz : f z=n <;> simp [hz]

end Percolation.BenjaminiSchramm

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma adjustedCeilingBandCount_eq_restrictedLayerCount
    (a : V → ℝ) (c l u : ℝ) (ω : Set E) (x : V) :
    G.adjustedCeilingBandCount a c l u ω x = restrictedLayerCount G.ends
      (Percolation.internalEdges G.ends {v | G.orbitAdjustedHeight a x v ≤ c})
      {v | l ≤ G.orbitAdjustedHeight a x v ∧ G.orbitAdjustedHeight a x v ≤ u} ω x := by
  apply tsum_congr
  intro y
  by_cases hc : Percolation.Conn G.ends
      (ω ∩ Percolation.internalEdges G.ends {v | G.orbitAdjustedHeight a x v ≤ c}) x y
  <;> by_cases hl : l ≤ G.orbitAdjustedHeight a x y
  <;> by_cases hu : G.orbitAdjustedHeight a x y ≤ u
  <;> simp [adjustedCeilingBandTransport,hc,hl,hu]

theorem expected_ceilingBandCount_le_intermediate_upLayerMoment [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e →
      |G.orbitAdjustedHeight a v w| ≤ R)
    (p : unitInterval) (C : ℝ≥0∞)
    (hrow : ∀ z, (∑' y, G.law p {ω | Percolation.Conn G.ends ω z y}) ≤ C)
    (n : ℕ) (hn : 0 < n) (x : V) (c l u : ℝ) (hlower : R*n ≤ l) :
    (∫⁻ ω, G.adjustedCeilingBandCount a c l u ω x ∂G.law p) ≤
      G.adjustedUpLayerMoment a R p n x 0*C := by
  simp_rw [G.adjustedCeilingBandCount_eq_restrictedLayerCount a c l u]
  let f := G.adjustedLayerIndex a R 0 x
  have hj : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e → f w ≤ f v+1 ∧ f v ≤ f w+1 := by
    intro e v w hv hw
    have hh := G.adjustedLayerIndex_edge_jump hc hl a R 0 hR hjump x v w e hv hw
    dsimp only [f]
    exact ⟨hh.2,by omega⟩
  have hx : f x < (n : ℤ) := by
    simp only [f,G.adjustedLayerIndex_self]
    exact_mod_cast hn
  have hA : ∀ y ∈ {v | l ≤ G.orbitAdjustedHeight a x v ∧ G.orbitAdjustedHeight a x v ≤ u},
      (n : ℤ) ≤ f y := by
    intro y hy
    simp only [f,adjustedLayerIndex,add_zero,Int.floor_zero,sub_zero]
    apply Int.le_floor.mpr
    apply (le_div_iff₀ hR).mpr
    have hlow : (n : ℝ)*R ≤ l := by nlinarith [hlower]
    exact hlow.trans hy.1
  exact first_layer_moment_bound_with_row G.ends p C hrow f hj _ _ x n hx hA

end CriticalPercolation.BondGraph

end

end OAI
