import OAI.Probability.BenjaminiSchramm.FractionalBandGeometry

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm

lemma ennreal_mul_negative_rpow_le (X : ℝ≥0∞) {δ : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ < 1) : X*X^(-δ) ≤ X^(1-δ) := by
  by_cases hzero : X=0
  · simp only [hzero,zero_mul,ENNReal.zero_rpow_of_pos (sub_pos.mpr hδ1),le_refl]
  by_cases htop : X=⊤
  · subst X
    by_cases hδ0 : δ=0
    · simp [hδ0]
    · have hδpos : 0 < δ := lt_of_le_of_ne hδ (Ne.symm hδ0)
      rw [ENNReal.top_rpow_of_neg (neg_neg_of_pos hδpos),mul_zero]
      exact bot_le
  apply le_of_eq
  calc
    _ = X^(1 : ℝ)*X^(-δ) := congrArg (fun Y => Y*X^(-δ)) (ENNReal.rpow_one X).symm
    _ = _ := (ENNReal.rpow_add 1 (-δ) hzero htop).symm

end Percolation.BenjaminiSchramm

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma fractionalReverseBandTransport_outgoing (a : V → ℝ) (c l u : ℝ)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ < 1) (ω : Set E) (x : V) :
    (∑' y, G.fractionalReverseBandTransport a c l u δ ω x y) ≤
      (G.adjustedCeilingBandCount a (c-u) (-u) (-l) ω x)^(1-δ) := by
  unfold fractionalReverseBandTransport
  rw [ENNReal.tsum_mul_right]
  exact ennreal_mul_negative_rpow_le _ hδ hδ1

lemma fractionalReverseBandTransport_incoming_sum
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (c l u : ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (ω : Set E) (x : V) :
    ENNReal.ofReal (Real.exp l)*
      (G.adjustedCeilingBandCount a (c-(u-l)) l u ω x *
        (G.adjustedCeilingBandCount a c (l-u) (u-l) ω x)^(-δ)) ≤
      ∑' y, G.fractionalReverseBandTransport a c l u δ ω y x *
        ENNReal.ofReal (Real.exp (G.orbitAdjustedHeight a x y)) := by
  rw [adjustedCeilingBandCount,←ENNReal.tsum_mul_right,←ENNReal.tsum_mul_left]
  exact ENNReal.tsum_le_tsum fun y =>
    G.fractionalReverseBandTransport_incoming_lower hc hl a c l u hδ ω x y

variable [Countable V] [Countable E]

lemma measurable_fractionalReverseBandTransport (a : V → ℝ) (c l u δ : ℝ) (x y : V) :
    Measurable (fun ω => G.fractionalReverseBandTransport a c l u δ ω x y) :=
  (G.measurable_adjustedCeilingBandTransport a _ _ _ x y).mul
    ((G.measurable_adjustedCeilingBandCount a _ _ _ x).pow_const (-δ))

omit [Countable V] [Countable E] in
lemma fractionalReverseBandTransport_aut (a : V → ℝ)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x) (c l u δ : ℝ)
    (φ : G.Aut) (ω : Set E) (x y : V) :
    G.fractionalReverseBandTransport a c l u δ (φ.edge '' ω) (φ.vertex x) (φ.vertex y) =
      G.fractionalReverseBandTransport a c l u δ ω x y := by
  simp only [fractionalReverseBandTransport,G.adjustedCeilingBandTransport_aut a ha,
    G.adjustedCeilingBandCount_aut a ha]

theorem expected_fractional_band_transport
    (O : G.OrbitRepresentatives) (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (hapos : ∀ x, 0 < a x)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x)
    (p : unitInterval) (c l u : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ < 1) :
    (∑ x ∈ O.roots, ENNReal.ofReal (a x)*(∫⁻ ω,
      G.adjustedCeilingBandCount a (c-(u-l)) l u ω x *
        (G.adjustedCeilingBandCount a c (l-u) (u-l) ω x)^(-δ) ∂G.law p)) ≤
      ENNReal.ofReal (Real.exp (-l)) *
        (∑ x ∈ O.roots, ENNReal.ofReal (a x)*(∫⁻ ω,
          (G.adjustedCeilingBandCount a (c-u) (-u) (-l) ω x)^(1-δ) ∂G.law p)) := by
  let B (ω : Set E) (x : V) := G.adjustedCeilingBandCount a (c-(u-l)) l u ω x *
    (G.adjustedCeilingBandCount a c (l-u) (u-l) ω x)^(-δ)
  have he := OrbitRepresentatives.random_normalized_tilted_transport G O hc hl a hapos ha p
    (G.fractionalReverseBandTransport a c l u δ)
    (G.measurable_fractionalReverseBandTransport a c l u δ)
    (G.fractionalReverseBandTransport_aut a ha c l u δ)
  have hw : ENNReal.ofReal (Real.exp l)*
      (∑ x ∈ O.roots, ENNReal.ofReal (a x)*(∫⁻ ω, B ω x ∂G.law p)) ≤
      ∑ x ∈ O.roots, ENNReal.ofReal (a x)*(∫⁻ ω,
        (G.adjustedCeilingBandCount a (c-u) (-u) (-l) ω x)^(1-δ) ∂G.law p) := by
    calc
      _ ≤ ∑ x ∈ O.roots, ENNReal.ofReal (a x)*(∫⁻ ω,
          ∑' y, G.fractionalReverseBandTransport a c l u δ ω y x *
            ENNReal.ofReal (Real.exp (G.orbitAdjustedHeight a x y)) ∂G.law p) := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro x hx
        calc
          _ = ENNReal.ofReal (a x)*(∫⁻ ω, ENNReal.ofReal (Real.exp l)*B ω x ∂G.law p) := by
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            ring
          _ ≤ _ := mul_le_mul' le_rfl (lintegral_mono
            (G.fractionalReverseBandTransport_incoming_sum hc hl a c l u hδ · x))
      _ = ∑ x ∈ O.roots, ENNReal.ofReal (a x)*(∫⁻ ω,
          ∑' y, G.fractionalReverseBandTransport a c l u δ ω x y ∂G.law p) := he.symm
      _ ≤ _ := Finset.sum_le_sum fun x _ => mul_le_mul' le_rfl
        (lintegral_mono (G.fractionalReverseBandTransport_outgoing a c l u hδ hδ1 · x))
  calc
    _ = ENNReal.ofReal (Real.exp (-l))*(ENNReal.ofReal (Real.exp l)*
        (∑ x ∈ O.roots, ENNReal.ofReal (a x)*(∫⁻ ω, B ω x ∂G.law p))) := by
      rw [←mul_assoc,←ENNReal.ofReal_mul (Real.exp_nonneg _),←Real.exp_add,
        neg_add_cancel,Real.exp_zero,ENNReal.ofReal_one,one_mul]
    _ ≤ _ := mul_le_mul' le_rfl hw

end CriticalPercolation.BondGraph

end

end OAI
