import OAI.Probability.BenjaminiSchramm.CeilingBandTransport
import OAI.Probability.BenjaminiSchramm.FreshSlabConcatenation

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

def adjustedHalfspaceConn (a : V → ℝ) (b : ℝ) (ω : Set E) (base x y : V) : Prop :=
  Percolation.Conn G.ends (ω ∩ Percolation.internalEdges G.ends
    {z | b ≤ G.orbitAdjustedHeight a base z}) x y

def adjustedStrictHalfspacePeak (a : V → ℝ) (b : ℝ) (ω : Set E) (base x : V) : Prop :=
  ∀ z, G.adjustedHalfspaceConn a b ω base x z → z ≠ x → G.orbitAdjustedHeight a x z < 0

lemma adjustedStrictHalfspacePeak_unique
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (a : V → ℝ) (b : ℝ)
    (ω : Set E) (base x y : V)
    (hxy : G.adjustedHalfspaceConn a b ω base x y)
    (hx : G.adjustedStrictHalfspacePeak a b ω base x)
    (hy : G.adjustedStrictHalfspacePeak a b ω base y) : x=y := by
  by_contra hne
  have hh := hx y hxy (Ne.symm hne)
  have hh' := hy x (Percolation.conn_symm G.ends _ hxy) hne
  rw [G.orbitAdjustedHeight_reverse hc hl a x y] at hh'
  linarith

def strictPeakBandTransport (a : V → ℝ) (r l u : ℝ)
    (ω : Set E) (y x : V) : ℝ≥0∞ :=
  if G.adjustedHalfspaceConn a (-r) ω y y x ∧
    G.adjustedStrictHalfspacePeak a (-r) ω y x ∧
      -u ≤ G.orbitAdjustedHeight a y x ∧ G.orbitAdjustedHeight a y x ≤ -l then 1 else 0

def strictPeakSlabBandTransport (a : V → ℝ) (r l u : ℝ)
    (ω : Set E) (x y : V) : ℝ≥0∞ :=
  if G.adjustedStrictHalfspacePeak a (l-r) ω x x ∧
    Percolation.Conn G.ends (ω ∩ Percolation.internalEdges G.ends
      {z | u-r ≤ G.orbitAdjustedHeight a x z ∧ G.orbitAdjustedHeight a x z ≤ 0}) x y ∧
      l ≤ G.orbitAdjustedHeight a x y ∧ G.orbitAdjustedHeight a x y ≤ u then 1 else 0

def strictPeakSlabBandCount (a : V → ℝ) (r l u : ℝ)
    (ω : Set E) (x : V) : ℝ≥0∞ := ∑' y, G.strictPeakSlabBandTransport a r l u ω x y

lemma strictPeakBandTransport_outgoing
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (a : V → ℝ) (r l u : ℝ)
    (ω : Set E) (y : V) :
    (∑' x, G.strictPeakBandTransport a r l u ω y x) ≤
      if ω ∈ restrictedHit G.ends (Percolation.internalEdges G.ends
        {z | -r ≤ G.orbitAdjustedHeight a y z}) y
          {z | -u ≤ G.orbitAdjustedHeight a y z} then 1 else 0 := by
  let P (x : V) := G.adjustedHalfspaceConn a (-r) ω y y x ∧
    G.adjustedStrictHalfspacePeak a (-r) ω y x ∧
      -u ≤ G.orbitAdjustedHeight a y x ∧ G.orbitAdjustedHeight a y x ≤ -l
  by_cases hex : ∃ x, P x
  · obtain ⟨x,hx⟩ := hex
    have hhit : ω ∈ restrictedHit G.ends (Percolation.internalEdges G.ends
        {z | -r ≤ G.orbitAdjustedHeight a y z}) y {z | -u ≤ G.orbitAdjustedHeight a y z} :=
      ⟨x,hx.2.2.1,hx.1⟩
    rw [ite_eq_left hhit,tsum_eq_single x]
    · exact (ite_eq_left hx).le
    · intro z hzx
      apply ite_eq_right
      intro hz
      exact hzx (G.adjustedStrictHalfspacePeak_unique hc hl a (-r) ω y z x
        ((Percolation.conn_symm G.ends _ hz.1).trans hx.1) hz.2.1 hx.2.1)
  · have hz (x : V) : G.strictPeakBandTransport a r l u ω y x=0 :=
      ite_eq_right (fun h => hex ⟨x,h⟩)
    rw [ENNReal.tsum_eq_zero.mpr hz]
    exact bot_le

lemma strictPeakSlabBandTransport_incoming_lower
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (a : V → ℝ) (r l u : ℝ)
    (ω : Set E) (x y : V) :
    ENNReal.ofReal (Real.exp l)*G.strictPeakSlabBandTransport a r l u ω x y ≤
      G.strictPeakBandTransport a r l u ω y x *
        ENNReal.ofReal (Real.exp (G.orbitAdjustedHeight a x y)) := by
  by_cases hp : G.adjustedStrictHalfspacePeak a (l-r) ω x x ∧
      Percolation.Conn G.ends (ω ∩ Percolation.internalEdges G.ends
        {z | u-r ≤ G.orbitAdjustedHeight a x z ∧ G.orbitAdjustedHeight a x z ≤ 0}) x y ∧
        l ≤ G.orbitAdjustedHeight a x y ∧ G.orbitAdjustedHeight a x y ≤ u
  · have hconn : G.adjustedHalfspaceConn a (-r) ω y y x := by
      apply Percolation.conn_symm G.ends _
      apply Percolation.conn_mono G.ends (Set.inter_subset_inter_right _
        (Percolation.internalEdges_mono G.ends ?_)) hp.2.1
      intro z hz
      have hh := G.orbitAdjustedHeight_change_base hc hl a x y z
      change u-r ≤ G.orbitAdjustedHeight a x z ∧ _ at hz
      change -r ≤ G.orbitAdjustedHeight a y z
      linarith [hp.2.2.2,hz.1]
    have hpeak : G.adjustedStrictHalfspacePeak a (-r) ω y x := by
      intro z hz hzx
      apply hp.1 z _ hzx
      apply Percolation.conn_mono G.ends (Set.inter_subset_inter_right _
        (Percolation.internalEdges_mono G.ends ?_)) hz
      intro v hv
      have hh := G.orbitAdjustedHeight_change_base hc hl a x y v
      change -r ≤ G.orbitAdjustedHeight a y v at hv
      change l-r ≤ G.orbitAdjustedHeight a x v
      linarith [hp.2.2.1]
    have ht : G.adjustedHalfspaceConn a (-r) ω y y x ∧
        G.adjustedStrictHalfspacePeak a (-r) ω y x ∧
          -u ≤ G.orbitAdjustedHeight a y x ∧ G.orbitAdjustedHeight a y x ≤ -l := by
      rw [G.orbitAdjustedHeight_reverse hc hl a x y]
      exact ⟨hconn,hpeak,by linarith [hp.2.2.2],by linarith [hp.2.2.1]⟩
    simp only [strictPeakSlabBandTransport,strictPeakBandTransport,ite_eq_left hp,
      ite_eq_left ht,mul_one,one_mul]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hp.2.2.1)
  · simp only [strictPeakSlabBandTransport,ite_eq_right hp,mul_zero]
    exact bot_le

end CriticalPercolation.BondGraph

end

end OAI
