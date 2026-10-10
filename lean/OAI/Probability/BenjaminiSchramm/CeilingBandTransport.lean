import OAI.Probability.BenjaminiSchramm.NormalizedLayerTransport
import OAI.Probability.BenjaminiSchramm.LayerFrontierGeometry

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

def adjustedCeilingBandTransport (a : V → ℝ) (c l u : ℝ)
    (ω : Set E) (x y : V) : ℝ≥0∞ :=
  if Percolation.Conn G.ends (ω ∩ Percolation.internalEdges G.ends
      {z | G.orbitAdjustedHeight a x z ≤ c}) x y ∧
      l ≤ G.orbitAdjustedHeight a x y ∧ G.orbitAdjustedHeight a x y ≤ u then 1 else 0

def adjustedCeilingBandCount (a : V → ℝ) (c l u : ℝ)
    (ω : Set E) (x : V) : ℝ≥0∞ :=
  ∑' y, G.adjustedCeilingBandTransport a c l u ω x y

lemma measurable_adjustedCeilingBandTransport [Countable V] [Countable E]
    (a : V → ℝ) (c l u : ℝ) (x y : V) :
    Measurable (fun ω => G.adjustedCeilingBandTransport a c l u ω x y) := by
  have hm : Measurable (fun ω : Set E => ω ∩ Percolation.internalEdges G.ends
      {z | G.orbitAdjustedHeight a x z ≤ c}) :=
    measurable_set_iff.mpr fun e => (measurable_set_mem e).and measurable_const
  exact Measurable.ite (((Percolation.measurableSet_conn G.ends x y).mem.comp hm).and
    measurable_const).setOf measurable_const measurable_const

lemma adjustedCeilingBandTransport_aut (a : V → ℝ)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x) (c l u : ℝ)
    (φ : G.Aut) (ω : Set E) (x y : V) :
    G.adjustedCeilingBandTransport a c l u (φ.edge '' ω) (φ.vertex x) (φ.vertex y) =
      G.adjustedCeilingBandTransport a c l u ω x y := by
  have hD : φ.vertex ⁻¹' {z | G.orbitAdjustedHeight a (φ.vertex x) z ≤ c} =
      {z | G.orbitAdjustedHeight a x z ≤ c} := by
    ext z
    simp only [Set.mem_preimage,Set.mem_ofPred_eq,G.orbitAdjustedHeight_aut a ha]
  have hmask : φ.edge ⁻¹' (φ.edge '' ω ∩ Percolation.internalEdges G.ends
      {z | G.orbitAdjustedHeight a (φ.vertex x) z ≤ c}) =
      ω ∩ Percolation.internalEdges G.ends {z | G.orbitAdjustedHeight a x z ≤ c} := by
    rw [Set.preimage_inter,Set.preimage_image_eq _ φ.edge.injective,
      ←Percolation.internalEdges_aut_preimage G.ends φ.preserves,hD]
  unfold adjustedCeilingBandTransport
  rw [←Percolation.conn_aut_iff G.ends φ.preserves,hmask,
    G.orbitAdjustedHeight_aut a ha]

lemma adjusted_ceiling_connection_change_root
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (ω : Set E) (x y v w : V) (c d : ℝ)
    (hcd : c ≤ d+G.orbitAdjustedHeight a x y)
    (hconn : Percolation.Conn G.ends (ω ∩ Percolation.internalEdges G.ends
      {z | G.orbitAdjustedHeight a x z ≤ c}) v w) :
    Percolation.Conn G.ends (ω ∩ Percolation.internalEdges G.ends
      {z | G.orbitAdjustedHeight a y z ≤ d}) v w := by
  apply Percolation.conn_mono G.ends (Set.inter_subset_inter_right _
    (Percolation.internalEdges_mono G.ends ?_)) hconn
  intro z hz
  change G.orbitAdjustedHeight a x z ≤ c at hz
  have hh := G.orbitAdjustedHeight_change_base hc hl a x y z
  change G.orbitAdjustedHeight a y z ≤ d
  linarith

lemma adjustedCeilingBandTransport_weight_bounds
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (c l u : ℝ) (ω : Set E) (x y : V) :
    ENNReal.ofReal (Real.exp (-u))*G.adjustedCeilingBandTransport a (c-u) (-u) (-l) ω y x ≤
      G.adjustedCeilingBandTransport a c l u ω x y*
        ENNReal.ofReal (Real.exp (G.orbitAdjustedHeight a y x)) ∧
    G.adjustedCeilingBandTransport a c l u ω x y*
        ENNReal.ofReal (Real.exp (G.orbitAdjustedHeight a y x)) ≤
      ENNReal.ofReal (Real.exp (-l))*G.adjustedCeilingBandTransport a (c-l) (-u) (-l) ω y x := by
  have hrev := G.orbitAdjustedHeight_reverse hc hl a x y
  constructor
  · by_cases ht : Percolation.Conn G.ends (ω ∩ Percolation.internalEdges G.ends
        {z | G.orbitAdjustedHeight a y z ≤ c-u}) y x ∧
        -u ≤ G.orbitAdjustedHeight a y x ∧ G.orbitAdjustedHeight a y x ≤ -l
    · have hs : Percolation.Conn G.ends (ω ∩ Percolation.internalEdges G.ends
          {z | G.orbitAdjustedHeight a x z ≤ c}) x y ∧
          l ≤ G.orbitAdjustedHeight a x y ∧ G.orbitAdjustedHeight a x y ≤ u := by
        refine ⟨G.adjusted_ceiling_connection_change_root hc hl a ω y x x y (c-u) c
          (by linarith [ht.2.1]) (Percolation.conn_symm G.ends _ ht.1),
          by linarith [ht.2.2],by linarith [ht.2.1]⟩
      simp only [adjustedCeilingBandTransport,ite_eq_left ht,ite_eq_left hs,mul_one,one_mul]
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ht.2.1)
    · simp only [adjustedCeilingBandTransport,ite_eq_right ht,mul_zero]
      exact bot_le
  · by_cases hs : Percolation.Conn G.ends (ω ∩ Percolation.internalEdges G.ends
        {z | G.orbitAdjustedHeight a x z ≤ c}) x y ∧
        l ≤ G.orbitAdjustedHeight a x y ∧ G.orbitAdjustedHeight a x y ≤ u
    · have ht : Percolation.Conn G.ends (ω ∩ Percolation.internalEdges G.ends
          {z | G.orbitAdjustedHeight a y z ≤ c-l}) y x ∧
          -u ≤ G.orbitAdjustedHeight a y x ∧ G.orbitAdjustedHeight a y x ≤ -l := by
        refine ⟨G.adjusted_ceiling_connection_change_root hc hl a ω x y y x c (c-l)
          (by linarith [hs.2.1]) (Percolation.conn_symm G.ends _ hs.1),
          by linarith [hs.2.2],by linarith [hs.2.1]⟩
      simp only [adjustedCeilingBandTransport,ite_eq_left ht,ite_eq_left hs,mul_one,one_mul]
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ht.2.2)
    · simp only [adjustedCeilingBandTransport,ite_eq_right hs,zero_mul]
      exact bot_le

theorem expected_adjustedCeilingBandCount_reciprocity [Countable V] [Countable E]
    (O : G.OrbitRepresentatives) (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (hapos : ∀ x, 0 < a x)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x) (p : unitInterval) (c l u : ℝ) :
    ENNReal.ofReal (Real.exp (-u))*
      (∑ x ∈ O.roots, ENNReal.ofReal (a x)*
        (∫⁻ ω, G.adjustedCeilingBandCount a (c-u) (-u) (-l) ω x ∂G.law p)) ≤
      (∑ x ∈ O.roots, ENNReal.ofReal (a x)*
        (∫⁻ ω, G.adjustedCeilingBandCount a c l u ω x ∂G.law p)) ∧
    (∑ x ∈ O.roots, ENNReal.ofReal (a x)*
        (∫⁻ ω, G.adjustedCeilingBandCount a c l u ω x ∂G.law p)) ≤
      ENNReal.ofReal (Real.exp (-l))*
        (∑ x ∈ O.roots, ENNReal.ofReal (a x)*
          (∫⁻ ω, G.adjustedCeilingBandCount a (c-l) (-u) (-l) ω x ∂G.law p)) := by
  have he := OrbitRepresentatives.random_normalized_tilted_transport G O hc hl a hapos ha p
    (G.adjustedCeilingBandTransport a c l u) (G.measurable_adjustedCeilingBandTransport a c l u)
    (G.adjustedCeilingBandTransport_aut a ha c l u)
  change (∑ x ∈ O.roots, ENNReal.ofReal (a x)*
    (∫⁻ ω, G.adjustedCeilingBandCount a c l u ω x ∂G.law p)) = _ at he
  rw [he]
  constructor
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro y _
    have hb (ω : Set E) : ENNReal.ofReal (Real.exp (-u))*
        G.adjustedCeilingBandCount a (c-u) (-u) (-l) ω y ≤
        ∑' x, G.adjustedCeilingBandTransport a c l u ω x y*
          ENNReal.ofReal (Real.exp (G.orbitAdjustedHeight a y x)) := by
      rw [adjustedCeilingBandCount,←ENNReal.tsum_mul_left]
      exact ENNReal.tsum_le_tsum fun x =>
        (G.adjustedCeilingBandTransport_weight_bounds hc hl a c l u ω x y).1
    calc
      _ = ENNReal.ofReal (a y)*(∫⁻ ω, ENNReal.ofReal (Real.exp (-u))*
          G.adjustedCeilingBandCount a (c-u) (-u) (-l) ω y ∂G.law p) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        ring
      _ ≤ _ := mul_le_mul' le_rfl (lintegral_mono hb)
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro y _
    have hb (ω : Set E) :
        (∑' x, G.adjustedCeilingBandTransport a c l u ω x y*
          ENNReal.ofReal (Real.exp (G.orbitAdjustedHeight a y x))) ≤
        ENNReal.ofReal (Real.exp (-l))*
          G.adjustedCeilingBandCount a (c-l) (-u) (-l) ω y := by
      rw [adjustedCeilingBandCount,←ENNReal.tsum_mul_left]
      exact ENNReal.tsum_le_tsum fun x =>
        (G.adjustedCeilingBandTransport_weight_bounds hc hl a c l u ω x y).2
    calc
      _ ≤ ENNReal.ofReal (a y)*(∫⁻ ω, ENNReal.ofReal (Real.exp (-l))*
          G.adjustedCeilingBandCount a (c-l) (-u) (-l) ω y ∂G.law p) :=
        mul_le_mul' le_rfl (lintegral_mono hb)
      _ = _ := by rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]; ring

end CriticalPercolation.BondGraph

end

end OAI
