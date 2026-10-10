import OAI.Probability.BenjaminiSchramm.CeilingBandUniform
import OAI.Probability.BenjaminiSchramm.FractionalHolder

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma reverse_ceiling_band_count_le_zero_band
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (c l u : ℝ) (ω : Set E) (x y : V)
    (hxy : Percolation.Conn G.ends (ω ∩ Percolation.internalEdges G.ends
      {z | G.orbitAdjustedHeight a x z ≤ c-(u-l)}) x y)
    (hylo : l ≤ G.orbitAdjustedHeight a x y) (hyhi : G.orbitAdjustedHeight a x y ≤ u) :
    G.adjustedCeilingBandCount a (c-u) (-u) (-l) ω y ≤
      G.adjustedCeilingBandCount a c (l-u) (u-l) ω x := by
  have hxy' := G.adjusted_ceiling_connection_change_root hc hl a ω x y x y
    (c-(u-l)) (c-u) (by linarith) hxy
  apply ENNReal.tsum_le_tsum
  intro z
  by_cases hz : Percolation.Conn G.ends (ω ∩ Percolation.internalEdges G.ends
      {v | G.orbitAdjustedHeight a y v ≤ c-u}) y z ∧
      -u ≤ G.orbitAdjustedHeight a y z ∧ G.orbitAdjustedHeight a y z ≤ -l
  · have hconn := G.adjusted_ceiling_connection_change_root hc hl a ω y x x z
      (c-u) c (by
        rw [G.orbitAdjustedHeight_reverse hc hl a x y]
        linarith) (hxy'.trans hz.1)
    have hh := G.orbitAdjustedHeight_change_base hc hl a x y z
    have ht : Percolation.Conn G.ends (ω ∩ Percolation.internalEdges G.ends
        {v | G.orbitAdjustedHeight a x v ≤ c}) x z ∧
        l-u ≤ G.orbitAdjustedHeight a x z ∧ G.orbitAdjustedHeight a x z ≤ u-l :=
      ⟨hconn,by linarith [hz.2.1],by linarith [hz.2.2]⟩
    simp only [adjustedCeilingBandTransport,ite_eq_left hz,ite_eq_left ht,le_refl]
  · simp only [adjustedCeilingBandTransport,ite_eq_right hz]
    exact bot_le

def fractionalReverseBandTransport (a : V → ℝ) (c l u δ : ℝ)
    (ω : Set E) (y x : V) : ℝ≥0∞ :=
  G.adjustedCeilingBandTransport a (c-u) (-u) (-l) ω y x *
    (G.adjustedCeilingBandCount a (c-u) (-u) (-l) ω y)^(-δ)

lemma fractionalReverseBandTransport_incoming_lower
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (c l u : ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (ω : Set E) (x y : V) :
    ENNReal.ofReal (Real.exp l)*
      (G.adjustedCeilingBandTransport a (c-(u-l)) l u ω x y *
        (G.adjustedCeilingBandCount a c (l-u) (u-l) ω x)^(-δ)) ≤
      G.fractionalReverseBandTransport a c l u δ ω y x *
        ENNReal.ofReal (Real.exp (G.orbitAdjustedHeight a x y)) := by
  by_cases hxy : Percolation.Conn G.ends (ω ∩ Percolation.internalEdges G.ends
      {z | G.orbitAdjustedHeight a x z ≤ c-(u-l)}) x y ∧
      l ≤ G.orbitAdjustedHeight a x y ∧ G.orbitAdjustedHeight a x y ≤ u
  · have hrev : Percolation.Conn G.ends (ω ∩ Percolation.internalEdges G.ends
        {z | G.orbitAdjustedHeight a y z ≤ c-u}) y x ∧
        -u ≤ G.orbitAdjustedHeight a y x ∧ G.orbitAdjustedHeight a y x ≤ -l := by
      rw [G.orbitAdjustedHeight_reverse hc hl a x y]
      exact ⟨Percolation.conn_symm G.ends _ (G.adjusted_ceiling_connection_change_root hc hl
        a ω x y x y (c-(u-l)) (c-u) (by linarith [hxy.2.1]) hxy.1),
        by linarith [hxy.2.2],by linarith [hxy.2.1]⟩
    simp only [fractionalReverseBandTransport,adjustedCeilingBandTransport,
      ite_eq_left hxy,ite_eq_left hrev,one_mul]
    have hpow : (G.adjustedCeilingBandCount a c (l-u) (u-l) ω x)^(-δ) ≤
        (G.adjustedCeilingBandCount a (c-u) (-u) (-l) ω y)^(-δ) := by
      simp only [ENNReal.rpow_neg]
      exact ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow
        (G.reverse_ceiling_band_count_le_zero_band hc hl a c l u ω x y hxy.1 hxy.2.1 hxy.2.2) hδ)
    exact (mul_le_mul' (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hxy.2.1)) hpow).trans_eq
      (mul_comm _ _)
  · simp only [adjustedCeilingBandTransport,ite_eq_right hxy,zero_mul,mul_zero]
    exact bot_le

end CriticalPercolation.BondGraph

end

end OAI
