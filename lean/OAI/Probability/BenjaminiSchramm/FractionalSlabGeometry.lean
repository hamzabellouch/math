import OAI.Probability.BenjaminiSchramm.FractionalBandTransport

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

def adjustedSlabBandTransport (a : V → ℝ) (d c l u : ℝ)
    (ω : Set E) (x y : V) : ℝ≥0∞ :=
  if Percolation.Conn G.ends (ω ∩ Percolation.internalEdges G.ends
      {z | d ≤ G.orbitAdjustedHeight a x z ∧ G.orbitAdjustedHeight a x z ≤ c}) x y ∧
      l ≤ G.orbitAdjustedHeight a x y ∧ G.orbitAdjustedHeight a x y ≤ u then 1 else 0

def adjustedSlabBandCount (a : V → ℝ) (d c l u : ℝ)
    (ω : Set E) (x : V) : ℝ≥0∞ :=
  ∑' y, G.adjustedSlabBandTransport a d c l u ω x y

lemma adjustedSlabBandCount_eq_restricted (a : V → ℝ) (d c l u : ℝ)
    (ω : Set E) (x : V) :
    G.adjustedSlabBandCount a d c l u ω x = restrictedLayerCount G.ends
      (Percolation.internalEdges G.ends {z | d ≤ G.orbitAdjustedHeight a x z ∧ G.orbitAdjustedHeight a x z ≤ c})
      {z | l ≤ G.orbitAdjustedHeight a x z ∧ G.orbitAdjustedHeight a x z ≤ u} ω x := by
  apply tsum_congr
  intro y
  unfold adjustedSlabBandTransport
  by_cases hc : Percolation.Conn G.ends
      (ω ∩ Percolation.internalEdges G.ends {z | d ≤ G.orbitAdjustedHeight a x z ∧ G.orbitAdjustedHeight a x z ≤ c}) x y
  <;> by_cases hl : l ≤ G.orbitAdjustedHeight a x y
  <;> by_cases hu : G.orbitAdjustedHeight a x y ≤ u
  <;> simp [hc,hl,hu]

lemma adjusted_slab_connection_change_root
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (a : V → ℝ)
    (ω : Set E) (x y v w : V) (d c d' c' : ℝ)
    (hlo : d'+G.orbitAdjustedHeight a x y ≤ d)
    (hhi : c ≤ c'+G.orbitAdjustedHeight a x y)
    (hconn : Percolation.Conn G.ends (ω ∩ Percolation.internalEdges G.ends
      {z | d ≤ G.orbitAdjustedHeight a x z ∧ G.orbitAdjustedHeight a x z ≤ c}) v w) :
    Percolation.Conn G.ends (ω ∩ Percolation.internalEdges G.ends
      {z | d' ≤ G.orbitAdjustedHeight a y z ∧ G.orbitAdjustedHeight a y z ≤ c'}) v w := by
  apply Percolation.conn_mono G.ends (Set.inter_subset_inter_right _
    (Percolation.internalEdges_mono G.ends ?_)) hconn
  intro z hz
  have hh := G.orbitAdjustedHeight_change_base hc hl a x y z
  exact ⟨by linarith [hz.1],by linarith [hz.2]⟩

lemma reverse_slab_band_count_le_zero_band
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (d c l u : ℝ) (ω : Set E) (x y : V)
    (hxy : Percolation.Conn G.ends (ω ∩ Percolation.internalEdges G.ends
      {z | d+(u-l) ≤ G.orbitAdjustedHeight a x z ∧ G.orbitAdjustedHeight a x z ≤ c-(u-l)}) x y)
    (hylo : l ≤ G.orbitAdjustedHeight a x y) (hyhi : G.orbitAdjustedHeight a x y ≤ u) :
    G.adjustedSlabBandCount a (d-l) (c-u) (-u) (-l) ω y ≤
      G.adjustedSlabBandCount a d c (l-u) (u-l) ω x := by
  have hxy' := G.adjusted_slab_connection_change_root hc hl a ω x y x y
    (d+(u-l)) (c-(u-l)) (d-l) (c-u) (by linarith) (by linarith) hxy
  apply ENNReal.tsum_le_tsum
  intro z
  by_cases hz : Percolation.Conn G.ends (ω ∩ Percolation.internalEdges G.ends
      {v | d-l ≤ G.orbitAdjustedHeight a y v ∧ G.orbitAdjustedHeight a y v ≤ c-u}) y z ∧
      -u ≤ G.orbitAdjustedHeight a y z ∧ G.orbitAdjustedHeight a y z ≤ -l
  · have hconn := G.adjusted_slab_connection_change_root hc hl a ω y x x z
      (d-l) (c-u) d c (by rw [G.orbitAdjustedHeight_reverse hc hl a x y]; linarith)
        (by rw [G.orbitAdjustedHeight_reverse hc hl a x y]; linarith) (hxy'.trans hz.1)
    have hh := G.orbitAdjustedHeight_change_base hc hl a x y z
    have ht : Percolation.Conn G.ends (ω ∩ Percolation.internalEdges G.ends
        {v | d ≤ G.orbitAdjustedHeight a x v ∧ G.orbitAdjustedHeight a x v ≤ c}) x z ∧
        l-u ≤ G.orbitAdjustedHeight a x z ∧ G.orbitAdjustedHeight a x z ≤ u-l :=
      ⟨hconn,by linarith [hz.2.1],by linarith [hz.2.2]⟩
    simp only [adjustedSlabBandTransport,ite_eq_left hz,ite_eq_left ht,le_refl]
  · simp only [adjustedSlabBandTransport,ite_eq_right hz]
    exact bot_le

def fractionalReverseSlabTransport (a : V → ℝ) (d c l u δ : ℝ)
    (ω : Set E) (y x : V) : ℝ≥0∞ :=
  G.adjustedSlabBandTransport a (d-l) (c-u) (-u) (-l) ω y x *
    (G.adjustedSlabBandCount a (d-l) (c-u) (-u) (-l) ω y)^(-δ)

lemma fractionalReverseSlabTransport_incoming_lower
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (d c l u : ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (ω : Set E) (x y : V) :
    ENNReal.ofReal (Real.exp l)*
      (G.adjustedSlabBandTransport a (d+(u-l)) (c-(u-l)) l u ω x y *
        (G.adjustedSlabBandCount a d c (l-u) (u-l) ω x)^(-δ)) ≤
      G.fractionalReverseSlabTransport a d c l u δ ω y x *
        ENNReal.ofReal (Real.exp (G.orbitAdjustedHeight a x y)) := by
  by_cases hxy : Percolation.Conn G.ends (ω ∩ Percolation.internalEdges G.ends
      {z | d+(u-l) ≤ G.orbitAdjustedHeight a x z ∧ G.orbitAdjustedHeight a x z ≤ c-(u-l)}) x y ∧
      l ≤ G.orbitAdjustedHeight a x y ∧ G.orbitAdjustedHeight a x y ≤ u
  · have hrev : Percolation.Conn G.ends (ω ∩ Percolation.internalEdges G.ends
        {z | d-l ≤ G.orbitAdjustedHeight a y z ∧ G.orbitAdjustedHeight a y z ≤ c-u}) y x ∧
        -u ≤ G.orbitAdjustedHeight a y x ∧ G.orbitAdjustedHeight a y x ≤ -l := by
      rw [G.orbitAdjustedHeight_reverse hc hl a x y]
      exact ⟨Percolation.conn_symm G.ends _ (G.adjusted_slab_connection_change_root hc hl a ω x y x y
        (d+(u-l)) (c-(u-l)) (d-l) (c-u) (by linarith [hxy.2.2])
          (by linarith [hxy.2.1]) hxy.1),by linarith [hxy.2.2],by linarith [hxy.2.1]⟩
    simp only [fractionalReverseSlabTransport,adjustedSlabBandTransport,
      ite_eq_left hxy,ite_eq_left hrev,one_mul]
    have hpow : (G.adjustedSlabBandCount a d c (l-u) (u-l) ω x)^(-δ) ≤
        (G.adjustedSlabBandCount a (d-l) (c-u) (-u) (-l) ω y)^(-δ) := by
      simp only [ENNReal.rpow_neg]
      exact ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow
        (G.reverse_slab_band_count_le_zero_band hc hl a d c l u ω x y hxy.1 hxy.2.1 hxy.2.2) hδ)
    exact (mul_le_mul' (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hxy.2.1)) hpow).trans_eq
      (mul_comm _ _)
  · simp only [adjustedSlabBandTransport,ite_eq_right hxy,zero_mul,mul_zero]
    exact bot_le

lemma adjustedSlabBandTransport_aut (a : V → ℝ)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x) (d c l u : ℝ)
    (φ : G.Aut) (ω : Set E) (x y : V) :
    G.adjustedSlabBandTransport a d c l u (φ.edge '' ω) (φ.vertex x) (φ.vertex y) =
      G.adjustedSlabBandTransport a d c l u ω x y := by
  have hD : φ.vertex ⁻¹' {z | d ≤ G.orbitAdjustedHeight a (φ.vertex x) z ∧
      G.orbitAdjustedHeight a (φ.vertex x) z ≤ c} =
      {z | d ≤ G.orbitAdjustedHeight a x z ∧ G.orbitAdjustedHeight a x z ≤ c} := by
    ext z
    simp only [Set.mem_preimage,Set.mem_ofPred_eq,G.orbitAdjustedHeight_aut a ha]
  have hmask : φ.edge ⁻¹' (φ.edge '' ω ∩ Percolation.internalEdges G.ends
      {z | d ≤ G.orbitAdjustedHeight a (φ.vertex x) z ∧ G.orbitAdjustedHeight a (φ.vertex x) z ≤ c}) =
      ω ∩ Percolation.internalEdges G.ends {z | d ≤ G.orbitAdjustedHeight a x z ∧ G.orbitAdjustedHeight a x z ≤ c} := by
    rw [Set.preimage_inter,Set.preimage_image_eq _ φ.edge.injective,
      ←Percolation.internalEdges_aut_preimage G.ends φ.preserves,hD]
  unfold adjustedSlabBandTransport
  rw [←Percolation.conn_aut_iff G.ends φ.preserves,hmask,G.orbitAdjustedHeight_aut a ha]

lemma adjustedSlabBandCount_aut (a : V → ℝ)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x) (d c l u : ℝ)
    (φ : G.Aut) (ω : Set E) (x : V) :
    G.adjustedSlabBandCount a d c l u (φ.edge '' ω) (φ.vertex x) =
      G.adjustedSlabBandCount a d c l u ω x := by
  unfold adjustedSlabBandCount
  rw [←φ.vertex.tsum_eq]
  simp only [G.adjustedSlabBandTransport_aut a ha]

variable [Countable V] [Countable E]

lemma measurable_adjustedSlabBandTransport (a : V → ℝ) (d c l u : ℝ) (x y : V) :
    Measurable (fun ω => G.adjustedSlabBandTransport a d c l u ω x y) := by
  have hm : Measurable (fun ω : Set E => ω ∩ Percolation.internalEdges G.ends
      {z | d ≤ G.orbitAdjustedHeight a x z ∧ G.orbitAdjustedHeight a x z ≤ c}) :=
    measurable_set_iff.mpr fun e => (measurable_set_mem e).and measurable_const
  exact Measurable.ite (((Percolation.measurableSet_conn G.ends x y).mem.comp hm).and
    measurable_const).setOf measurable_const measurable_const

lemma measurable_adjustedSlabBandCount (a : V → ℝ) (d c l u : ℝ) (x : V) :
    Measurable (fun ω => G.adjustedSlabBandCount a d c l u ω x) :=
  Measurable.tsum fun y => G.measurable_adjustedSlabBandTransport a d c l u x y

end CriticalPercolation.BondGraph

end

end OAI
