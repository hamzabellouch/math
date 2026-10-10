import OAI.Probability.BenjaminiSchramm.PeakHalfspaceGeometry

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma adjustedHalfspaceConn_aut (a : V → ℝ)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x) (b : ℝ)
    (φ : G.Aut) (ω : Set E) (base x y : V) :
    G.adjustedHalfspaceConn a b (φ.edge '' ω) (φ.vertex base) (φ.vertex x) (φ.vertex y) ↔
      G.adjustedHalfspaceConn a b ω base x y := by
  have hD : φ.vertex ⁻¹' {z | b ≤ G.orbitAdjustedHeight a (φ.vertex base) z} =
      {z | b ≤ G.orbitAdjustedHeight a base z} := by
    ext z
    simp only [Set.mem_preimage,Set.mem_ofPred_eq,G.orbitAdjustedHeight_aut a ha]
  have hmask : φ.edge ⁻¹' (φ.edge '' ω ∩ Percolation.internalEdges G.ends
      {z | b ≤ G.orbitAdjustedHeight a (φ.vertex base) z}) =
      ω ∩ Percolation.internalEdges G.ends {z | b ≤ G.orbitAdjustedHeight a base z} := by
    rw [Set.preimage_inter,Set.preimage_image_eq _ φ.edge.injective,
      ←Percolation.internalEdges_aut_preimage G.ends φ.preserves,hD]
  unfold adjustedHalfspaceConn
  rw [←Percolation.conn_aut_iff G.ends φ.preserves,hmask]

lemma adjustedStrictHalfspacePeak_aut (a : V → ℝ)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x) (b : ℝ)
    (φ : G.Aut) (ω : Set E) (base x : V) :
    G.adjustedStrictHalfspacePeak a b (φ.edge '' ω) (φ.vertex base) (φ.vertex x) =
      G.adjustedStrictHalfspacePeak a b ω base x := by
  apply propext
  constructor
  · intro h z hz hzx
    have hh := h (φ.vertex z) ((G.adjustedHalfspaceConn_aut a ha b φ ω base x z).mpr hz)
      (fun he => hzx (φ.vertex.injective he))
    simpa only [G.orbitAdjustedHeight_aut a ha] using hh
  · intro h z hz hzx
    obtain ⟨z,rfl⟩ := φ.vertex.surjective z
    have hh := h z ((G.adjustedHalfspaceConn_aut a ha b φ ω base x z).mp hz)
      (fun he => hzx (congrArg φ.vertex he))
    simpa only [G.orbitAdjustedHeight_aut a ha] using hh

lemma strictPeakBandTransport_aut (a : V → ℝ)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x) (r l u : ℝ)
    (φ : G.Aut) (ω : Set E) (y x : V) :
    G.strictPeakBandTransport a r l u (φ.edge '' ω) (φ.vertex y) (φ.vertex x) =
      G.strictPeakBandTransport a r l u ω y x := by
  simp only [strictPeakBandTransport,G.adjustedHalfspaceConn_aut a ha,
    G.adjustedStrictHalfspacePeak_aut a ha,G.orbitAdjustedHeight_aut a ha]

variable [Countable V] [Countable E]

lemma measurable_adjustedHalfspaceConn (a : V → ℝ) (b : ℝ) (base x y : V) :
    Measurable (fun ω => G.adjustedHalfspaceConn a b ω base x y) := by
  have hm : Measurable (fun ω : Set E => ω ∩ Percolation.internalEdges G.ends
      {z | b ≤ G.orbitAdjustedHeight a base z}) :=
    measurable_set_iff.mpr fun e => (measurable_set_mem e).and measurable_const
  exact (Percolation.measurableSet_conn G.ends x y).mem.comp hm

lemma measurable_adjustedStrictHalfspacePeak (a : V → ℝ) (b : ℝ) (base x : V) :
    Measurable (fun ω => G.adjustedStrictHalfspacePeak a b ω base x) := by
  exact Measurable.forall fun z => (G.measurable_adjustedHalfspaceConn a b base x z).imp
    (measurable_const.imp measurable_const)

lemma measurable_strictPeakBandTransport (a : V → ℝ) (r l u : ℝ) (y x : V) :
    Measurable (fun ω => G.strictPeakBandTransport a r l u ω y x) := by
  exact Measurable.ite (((G.measurable_adjustedHalfspaceConn a (-r) y y x).and
    ((G.measurable_adjustedStrictHalfspacePeak a (-r) y x).and measurable_const)).setOf)
      measurable_const measurable_const

lemma measurable_strictPeakSlabBandTransport (a : V → ℝ) (r l u : ℝ) (x y : V) :
    Measurable (fun ω => G.strictPeakSlabBandTransport a r l u ω x y) := by
  have hm : Measurable (fun ω : Set E => ω ∩ Percolation.internalEdges G.ends
      {z | u-r ≤ G.orbitAdjustedHeight a x z ∧ G.orbitAdjustedHeight a x z ≤ 0}) :=
    measurable_set_iff.mpr fun e => (measurable_set_mem e).and measurable_const
  exact Measurable.ite (((G.measurable_adjustedStrictHalfspacePeak a (l-r) x x).and
    (((Percolation.measurableSet_conn G.ends x y).mem.comp hm).and measurable_const)).setOf)
      measurable_const measurable_const

lemma measurable_strictPeakSlabBandCount (a : V → ℝ) (r l u : ℝ) (x : V) :
    Measurable (fun ω => G.strictPeakSlabBandCount a r l u ω x) :=
  Measurable.tsum fun y => G.measurable_strictPeakSlabBandTransport a r l u x y

theorem expected_strictPeakSlabBandCount_bound
    (O : G.OrbitRepresentatives) (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (hapos : ∀ x, 0 < a x)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x) (p : unitInterval) (r l u : ℝ) :
    ENNReal.ofReal (Real.exp l)*
      (∑ x ∈ O.roots, ENNReal.ofReal (a x)*
        (∫⁻ ω, G.strictPeakSlabBandCount a r l u ω x ∂G.law p)) ≤
      ∑ y ∈ O.roots, ENNReal.ofReal (a y)*G.law p
        (restrictedHit G.ends (Percolation.internalEdges G.ends
          {z | -r ≤ G.orbitAdjustedHeight a y z}) y {z | -u ≤ G.orbitAdjustedHeight a y z}) := by
  have hin (ω : Set E) (x : V) :
      ENNReal.ofReal (Real.exp l)*G.strictPeakSlabBandCount a r l u ω x ≤
        ∑' y, G.strictPeakBandTransport a r l u ω y x*
          ENNReal.ofReal (Real.exp (G.orbitAdjustedHeight a x y)) := by
    rw [strictPeakSlabBandCount,←ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum fun y =>
      G.strictPeakSlabBandTransport_incoming_lower hc hl a r l u ω x y
  calc
    _ = ∑ x ∈ O.roots, ENNReal.ofReal (a x)*
        (∫⁻ ω, ENNReal.ofReal (Real.exp l)*G.strictPeakSlabBandCount a r l u ω x ∂G.law p) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [lintegral_const_mul _ (G.measurable_strictPeakSlabBandCount a r l u x)]
      ring
    _ ≤ ∑ x ∈ O.roots, ENNReal.ofReal (a x)*
        (∫⁻ ω, ∑' y, G.strictPeakBandTransport a r l u ω y x*
          ENNReal.ofReal (Real.exp (G.orbitAdjustedHeight a x y)) ∂G.law p) :=
      Finset.sum_le_sum fun x _ => mul_le_mul' le_rfl (lintegral_mono fun ω => hin ω x)
    _ = ∑ y ∈ O.roots, ENNReal.ofReal (a y)*
        (∫⁻ ω, ∑' x, G.strictPeakBandTransport a r l u ω y x ∂G.law p) :=
      (OrbitRepresentatives.random_normalized_tilted_transport G O hc hl a hapos ha p
        (G.strictPeakBandTransport a r l u) (G.measurable_strictPeakBandTransport a r l u)
          (G.strictPeakBandTransport_aut a ha r l u)).symm
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro y _
      apply mul_le_mul' le_rfl
      apply (lintegral_mono fun ω => G.strictPeakBandTransport_outgoing hc hl a r l u ω y).trans_eq
      simpa only [Set.indicator,Pi.one_apply] using lintegral_indicator_one (μ := G.law p)
        (measurableSet_restrictedHit G.ends _ y _)

end CriticalPercolation.BondGraph

end

end OAI
