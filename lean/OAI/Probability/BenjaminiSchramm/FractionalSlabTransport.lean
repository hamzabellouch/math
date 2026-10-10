import OAI.Probability.BenjaminiSchramm.FractionalSlabGeometry

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma fractionalReverseSlabTransport_outgoing (a : V → ℝ) (d c l u : ℝ)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ < 1) (ω : Set E) (x : V) :
    (∑' y, G.fractionalReverseSlabTransport a d c l u δ ω x y) ≤
      (G.adjustedSlabBandCount a (d-l) (c-u) (-u) (-l) ω x)^(1-δ) := by
  unfold fractionalReverseSlabTransport
  rw [ENNReal.tsum_mul_right]
  exact ennreal_mul_negative_rpow_le _ hδ hδ1

lemma fractionalReverseSlabTransport_incoming_sum
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (d c l u : ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (ω : Set E) (x : V) :
    ENNReal.ofReal (Real.exp l)*
      (G.adjustedSlabBandCount a (d+(u-l)) (c-(u-l)) l u ω x *
        (G.adjustedSlabBandCount a d c (l-u) (u-l) ω x)^(-δ)) ≤
      ∑' y, G.fractionalReverseSlabTransport a d c l u δ ω y x *
        ENNReal.ofReal (Real.exp (G.orbitAdjustedHeight a x y)) := by
  rw [adjustedSlabBandCount,←ENNReal.tsum_mul_right,←ENNReal.tsum_mul_left]
  exact ENNReal.tsum_le_tsum fun y =>
    G.fractionalReverseSlabTransport_incoming_lower hc hl a d c l u hδ ω x y

variable [Countable V] [Countable E]

lemma measurable_fractionalReverseSlabTransport (a : V → ℝ) (d c l u δ : ℝ) (x y : V) :
    Measurable (fun ω => G.fractionalReverseSlabTransport a d c l u δ ω x y) :=
  (G.measurable_adjustedSlabBandTransport a _ _ _ _ x y).mul
    ((G.measurable_adjustedSlabBandCount a _ _ _ _ x).pow_const (-δ))

omit [Countable V] [Countable E] in
lemma fractionalReverseSlabTransport_aut (a : V → ℝ)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x) (d c l u δ : ℝ)
    (φ : G.Aut) (ω : Set E) (x y : V) :
    G.fractionalReverseSlabTransport a d c l u δ (φ.edge '' ω) (φ.vertex x) (φ.vertex y) =
      G.fractionalReverseSlabTransport a d c l u δ ω x y := by
  simp only [fractionalReverseSlabTransport,G.adjustedSlabBandTransport_aut a ha,
    G.adjustedSlabBandCount_aut a ha]

theorem expected_fractional_slab_transport
    (O : G.OrbitRepresentatives) (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (hapos : ∀ x, 0 < a x)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x)
    (p : unitInterval) (d c l u : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ < 1) :
    (∑ x ∈ O.roots, ENNReal.ofReal (a x)*(∫⁻ ω,
      G.adjustedSlabBandCount a (d+(u-l)) (c-(u-l)) l u ω x *
        (G.adjustedSlabBandCount a d c (l-u) (u-l) ω x)^(-δ) ∂G.law p)) ≤
      ENNReal.ofReal (Real.exp (-l)) *
        (∑ x ∈ O.roots, ENNReal.ofReal (a x)*(∫⁻ ω,
          (G.adjustedSlabBandCount a (d-l) (c-u) (-u) (-l) ω x)^(1-δ) ∂G.law p)) := by
  let B (ω : Set E) (x : V) := G.adjustedSlabBandCount a (d+(u-l)) (c-(u-l)) l u ω x *
    (G.adjustedSlabBandCount a d c (l-u) (u-l) ω x)^(-δ)
  have he := OrbitRepresentatives.random_normalized_tilted_transport G O hc hl a hapos ha p
    (G.fractionalReverseSlabTransport a d c l u δ)
    (G.measurable_fractionalReverseSlabTransport a d c l u δ)
    (G.fractionalReverseSlabTransport_aut a ha d c l u δ)
  have hw : ENNReal.ofReal (Real.exp l)*
      (∑ x ∈ O.roots, ENNReal.ofReal (a x)*(∫⁻ ω, B ω x ∂G.law p)) ≤
      ∑ x ∈ O.roots, ENNReal.ofReal (a x)*(∫⁻ ω,
        (G.adjustedSlabBandCount a (d-l) (c-u) (-u) (-l) ω x)^(1-δ) ∂G.law p) := by
    calc
      _ ≤ ∑ x ∈ O.roots, ENNReal.ofReal (a x)*(∫⁻ ω,
          ∑' y, G.fractionalReverseSlabTransport a d c l u δ ω y x *
            ENNReal.ofReal (Real.exp (G.orbitAdjustedHeight a x y)) ∂G.law p) := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro x hx
        calc
          _ = ENNReal.ofReal (a x)*(∫⁻ ω, ENNReal.ofReal (Real.exp l)*B ω x ∂G.law p) := by
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            ring
          _ ≤ _ := mul_le_mul' le_rfl (lintegral_mono
            (G.fractionalReverseSlabTransport_incoming_sum hc hl a d c l u hδ · x))
      _ = ∑ x ∈ O.roots, ENNReal.ofReal (a x)*(∫⁻ ω,
          ∑' y, G.fractionalReverseSlabTransport a d c l u δ ω x y ∂G.law p) := he.symm
      _ ≤ _ := Finset.sum_le_sum fun x _ => mul_le_mul' le_rfl
        (lintegral_mono (G.fractionalReverseSlabTransport_outgoing a d c l u hδ hδ1 · x))
  calc
    _ = ENNReal.ofReal (Real.exp (-l))*(ENNReal.ofReal (Real.exp l)*
        (∑ x ∈ O.roots, ENNReal.ofReal (a x)*(∫⁻ ω, B ω x ∂G.law p))) := by
      rw [←mul_assoc,←ENNReal.ofReal_mul (Real.exp_nonneg _),←Real.exp_add,
        neg_add_cancel,Real.exp_zero,ENNReal.ofReal_one,one_mul]
    _ ≤ _ := mul_le_mul' le_rfl hw

end CriticalPercolation.BondGraph

end

end OAI
