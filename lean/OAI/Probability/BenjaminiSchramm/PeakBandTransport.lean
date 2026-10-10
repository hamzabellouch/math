import OAI.Probability.BenjaminiSchramm.PeakBandProbability

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

def peakUpBandTransport (a : V → ℝ) (l u : ℝ) (ω : Set E) (y x : V) : ℝ≥0∞ :=
  if l < G.orbitAdjustedHeight a y x ∧ G.orbitAdjustedHeight a y x ≤ u ∧
    ω ∈ strictHeightPeakConnection G.ends (G.orbitAdjustedHeight a y) y x then 1 else 0

def peakDownBandCount (a : V → ℝ) (l u : ℝ) (ω : Set E) (x : V) : ℝ≥0∞ :=
  ∑' y, G.peakUpBandTransport a l u ω y x

lemma peakUpBandTransport_outgoing (a : V → ℝ) (l u : ℝ) (ω : Set E) (y : V) :
    (∑' x, G.peakUpBandTransport a l u ω y x) =
      (G.strictPeakBandEvent a l u y).indicator (fun _ => (1 : ℝ≥0∞)) ω := by
  by_cases he : ω ∈ G.strictPeakBandEvent a l u y
  · obtain ⟨z,hz⟩ := he
    rw [Set.indicator_of_mem (show ω ∈ G.strictPeakBandEvent a l u y from ⟨z,hz⟩),
      tsum_eq_single z]
    · exact ite_eq_left hz
    · intro x hxz
      apply ite_eq_right
      rintro ⟨_,_,hxy,hpeak⟩
      have hzx := Percolation.conn_trans G.ends ω (Percolation.conn_symm G.ends ω hz.2.2.1) hxy
      have hlt := hz.2.2.2 x hzx hxz
      have hlt' := hpeak z (Percolation.conn_symm G.ends ω hzx) (Ne.symm hxz)
      linarith
  · rw [Set.indicator_of_notMem he]
    apply ENNReal.tsum_eq_zero.mpr
    intro x
    exact ite_eq_right (fun hx => he ⟨x,hx⟩)

lemma peakUpBandTransport_incoming_bound
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (a : V → ℝ)
    (l u : ℝ) (ω : Set E) (x y : V) :
    G.peakUpBandTransport a l u ω y x*ENNReal.ofReal (Real.exp (G.orbitAdjustedHeight a x y)) ≤
      ENNReal.ofReal (Real.exp (-l))*G.peakUpBandTransport a l u ω y x := by
  by_cases h : l < G.orbitAdjustedHeight a y x ∧ G.orbitAdjustedHeight a y x ≤ u ∧
      ω ∈ strictHeightPeakConnection G.ends (G.orbitAdjustedHeight a y) y x
  · simp only [peakUpBandTransport,ite_eq_left h,one_mul,mul_one]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    rw [G.orbitAdjustedHeight_reverse hc hl a y x]
    linarith [h.1]
  · simp only [peakUpBandTransport,ite_eq_right h,zero_mul,mul_zero,le_refl]

variable [Countable V] [Countable E]

lemma measurable_peakUpBandTransport (a : V → ℝ) (l u : ℝ) (y x : V) :
    Measurable (fun ω => G.peakUpBandTransport a l u ω y x) := by
  exact Measurable.ite (measurable_const.and (measurable_const.and
    (measurableSet_strictHeightPeakConnection G.ends _ y x).mem)).setOf
      measurable_const measurable_const

lemma measurable_peakDownBandCount (a : V → ℝ) (l u : ℝ) (x : V) :
    Measurable (fun ω => G.peakDownBandCount a l u ω x) :=
  Measurable.tsum fun y => G.measurable_peakUpBandTransport a l u y x

omit [Countable V] [Countable E] in
lemma peakUpBandTransport_aut (a : V → ℝ)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x) (l u : ℝ)
    (φ : G.Aut) (ω : Set E) (y x : V) :
    G.peakUpBandTransport a l u (φ.edge '' ω) (φ.vertex y) (φ.vertex x)=
      G.peakUpBandTransport a l u ω y x := by
  have hpeak : φ.edge '' ω ∈ strictHeightPeakConnection G.ends
      (G.orbitAdjustedHeight a (φ.vertex y)) (φ.vertex y) (φ.vertex x) ↔
      ω ∈ strictHeightPeakConnection G.ends (G.orbitAdjustedHeight a y) y x := by
    have hconn (v w : V) : Percolation.Conn G.ends (φ.edge '' ω) (φ.vertex v) (φ.vertex w) ↔
        Percolation.Conn G.ends ω v w := by
      rw [←Percolation.conn_aut_iff G.ends φ.preserves,
        Set.preimage_image_eq _ φ.edge.injective]
    constructor
    · rintro ⟨h,hp⟩
      refine ⟨(hconn y x).mp h,fun z hz hzx => ?_⟩
      have hh := hp (φ.vertex z) ((hconn x z).mpr hz) (fun he => hzx (φ.vertex.injective he))
      simpa only [G.orbitAdjustedHeight_aut a ha] using hh
    · rintro ⟨h,hp⟩
      refine ⟨(hconn y x).mpr h,?_⟩
      intro z hz hzx
      obtain ⟨v,rfl⟩ := φ.vertex.surjective z
      have hh := hp v ((hconn x v).mp hz) (fun he => hzx (congrArg φ.vertex he))
      simpa only [G.orbitAdjustedHeight_aut a ha] using hh
  simp only [peakUpBandTransport,G.orbitAdjustedHeight_aut a ha,hpeak]

theorem expected_peakDownBandCount_lower
    (O : G.OrbitRepresentatives) (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (hapos : ∀ x, 0 < a x)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x) (p : unitInterval) (l u : ℝ) :
    (∑ y ∈ O.roots, ENNReal.ofReal (a y)*G.law p (G.strictPeakBandEvent a l u y)) ≤
      ENNReal.ofReal (Real.exp (-l))*
        (∑ x ∈ O.roots, ENNReal.ofReal (a x)*
          (∫⁻ ω, G.peakDownBandCount a l u ω x ∂G.law p)) := by
  have he := OrbitRepresentatives.random_normalized_tilted_transport G O hc hl a hapos ha p
    (G.peakUpBandTransport a l u) (G.measurable_peakUpBandTransport a l u)
      (G.peakUpBandTransport_aut a ha l u)
  simp_rw [G.peakUpBandTransport_outgoing,
    lintegral_indicator_fun_one (G.measurableSet_strictPeakBandEvent a l u _)] at he
  rw [he,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _hx
  calc
    _ ≤ ENNReal.ofReal (a x)*(∫⁻ ω,
        ENNReal.ofReal (Real.exp (-l))*G.peakDownBandCount a l u ω x ∂G.law p) := by
      apply mul_le_mul' le_rfl
      apply lintegral_mono
      intro ω
      change (∑' y, G.peakUpBandTransport a l u ω y x*ENNReal.ofReal (Real.exp (G.orbitAdjustedHeight a x y))) ≤
        ENNReal.ofReal (Real.exp (-l))*(∑' y, G.peakUpBandTransport a l u ω y x)
      rw [←ENNReal.tsum_mul_left]
      exact ENNReal.tsum_le_tsum fun y => G.peakUpBandTransport_incoming_bound hc hl a l u ω x y
    _ = _ := by
      rw [lintegral_const_mul _ (G.measurable_peakDownBandCount a l u x)]
      ring

end CriticalPercolation.BondGraph

end

end OAI
