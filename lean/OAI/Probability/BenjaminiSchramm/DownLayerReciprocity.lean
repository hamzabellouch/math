import OAI.Probability.BenjaminiSchramm.CeilingBandUniform

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma downLayerCount_le_ceilingBandCount
    (a : V → ℝ) (R : ℝ) (hR : 0 < R) (n : ℕ) (x : V) (u : ℝ) (ω : Set E) :
    restrictedLayerCount G.ends
      (Percolation.internalEdges G.ends {v | G.adjustedLayerIndex a R u x v ≤ 0})
      {v | G.adjustedLayerIndex a R u x v = -(n : ℤ)} ω x ≤
      G.adjustedCeilingBandCount a R (-(R*((n : ℝ)+1))) (-(R*((n : ℝ)-1))) ω x := by
  have hD : {v | G.adjustedLayerIndex a R u x v ≤ 0} ⊆
      {v | G.orbitAdjustedHeight a x v ≤ R} := by
    intro v hv
    have hh := (G.adjustedLayerIndex_height_bounds a R u hR x v).2
    have hi : (G.adjustedLayerIndex a R u x v : ℝ) ≤ 0 := by exact_mod_cast hv
    change G.orbitAdjustedHeight a x v ≤ R
    nlinarith
  apply ENNReal.tsum_le_tsum
  intro y
  by_cases hy : G.adjustedLayerIndex a R u x y = -(n : ℤ) ∧
      Percolation.Conn G.ends (ω ∩ Percolation.internalEdges G.ends
        {v | G.adjustedLayerIndex a R u x v ≤ 0}) x y
  · have hh := G.adjustedLayerIndex_height_bounds a R u hR x y
    rw [hy.1] at hh
    push_cast at hh
    have ht : Percolation.Conn G.ends (ω ∩ Percolation.internalEdges G.ends
        {v | G.orbitAdjustedHeight a x v ≤ R}) x y ∧
        -(R*((n : ℝ)+1)) ≤ G.orbitAdjustedHeight a x y ∧
        G.orbitAdjustedHeight a x y ≤ -(R*((n : ℝ)-1)) := by
      exact ⟨Percolation.conn_mono G.ends (Set.inter_subset_inter_right _
        (Percolation.internalEdges_mono G.ends hD)) hy.2,by linarith [hh.1],by linarith [hh.2]⟩
    simp only [Set.mem_ofPred_eq,adjustedCeilingBandTransport,ite_eq_left hy,ite_eq_left ht,le_refl]
  · simp only [Set.mem_ofPred_eq,ite_eq_right hy]
    exact bot_le

variable [Countable V] [Countable E]

theorem adjustedDownLayerMoment_le_shifted_up
    (O : G.OrbitRepresentatives) (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (hapos : ∀ x, 0 < a x)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x)
    (m : ℝ) (hm : 0 < m) (ham : ∀ x, m ≤ a x)
    (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e →
      |G.orbitAdjustedHeight a v w| ≤ R)
    (p : unitInterval) (C : ℝ≥0∞)
    (hrow : ∀ z, (∑' y, G.law p {ω | Percolation.Conn G.ends ω z y}) ≤ C)
    (n : ℕ) (hn : 3 ≤ n) (x : V) (u : ℝ) :
    G.adjustedDownLayerMoment a R p n x u ≤
      ((ENNReal.ofReal m)⁻¹*(∑ r ∈ O.roots, ENNReal.ofReal (a r)))*
        ENNReal.ofReal (Real.exp (R*((n : ℝ)+1)))*
          (G.supAdjustedUpLayerMoment a R p (n-2)*C) := by
  have hnm : 0 < n-2 := by omega
  have hmin : R*(n-2 : ℕ) ≤ -(-(R*((n : ℝ)-1))) := by
    rw [Nat.cast_sub (by omega : 2 ≤ n)]
    push_cast
    nlinarith
  have hsup : (⨆ y, ∫⁻ ω, G.adjustedCeilingBandCount a
      (R-(-(R*((n : ℝ)+1)))) (-(-(R*((n : ℝ)-1)))) (-(-(R*((n : ℝ)+1)))) ω y ∂G.law p) ≤
      G.supAdjustedUpLayerMoment a R p (n-2)*C := by
    apply iSup_le
    intro y
    exact (G.expected_ceilingBandCount_le_intermediate_upLayerMoment hc hl a R hR hjump
      p C hrow (n-2) hnm y _ _ _ hmin).trans
      (mul_le_mul' (G.adjustedUpLayerMoment_le_sup a R p (n-2) y 0) le_rfl)
  calc
    _ ≤ ∫⁻ ω, G.adjustedCeilingBandCount a R
        (-(R*((n : ℝ)+1))) (-(R*((n : ℝ)-1))) ω x ∂G.law p :=
      lintegral_mono (G.downLayerCount_le_ceilingBandCount a R hR n x u)
    _ ≤ _ := by
      have hh := (G.expected_ceilingBandCount_uniform_bound O hc hl a hapos ha m hm ham
        p R (-(R*((n : ℝ)+1))) (-(R*((n : ℝ)-1))) x).trans
        (mul_le_mul' le_rfl hsup)
      simpa only [neg_neg] using hh

end CriticalPercolation.BondGraph

end

end OAI
