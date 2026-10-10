import OAI.Probability.BenjaminiSchramm.FractionalBandTransport

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

lemma expected_band_product_aut (a : V → ℝ)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x) (c l u δ : ℝ)
    (φ : G.Aut) (p : unitInterval) (x : V) :
    (∫⁻ ω, G.adjustedCeilingBandCount a (c-(u-l)) l u ω (φ.vertex x) *
      (G.adjustedCeilingBandCount a c (l-u) (u-l) ω (φ.vertex x))^(-δ) ∂G.law p) =
    ∫⁻ ω, G.adjustedCeilingBandCount a (c-(u-l)) l u ω x *
      (G.adjustedCeilingBandCount a c (l-u) (u-l) ω x)^(-δ) ∂G.law p := by
  conv_lhs => rw [←G.law_map_aut p φ]
  have hm : Measurable (fun ω : Set E =>
      G.adjustedCeilingBandCount a (c-(u-l)) l u ω (φ.vertex x) *
        (G.adjustedCeilingBandCount a c (l-u) (u-l) ω (φ.vertex x))^(-δ)) :=
    (G.measurable_adjustedCeilingBandCount a _ _ _ _).mul
      ((G.measurable_adjustedCeilingBandCount a _ _ _ _).pow_const (-δ))
  rw [lintegral_map hm
      (BernoulliProduct.measurable_image_equiv φ.edge)]
  simp only [G.adjustedCeilingBandCount_aut a ha]

theorem fractional_ceiling_band_estimate
    (O : G.OrbitRepresentatives) (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (hapos : ∀ x, 0 < a x)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x)
    (m : ℝ) (hm : 0 < m) (ham : ∀ x, m ≤ a x)
    (p : unitInterval) (c l u : ℝ) (x : V)
    {α δ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hδ : 0 ≤ δ) (hδα : δ ≤ 1-α)
    (hZfin : ∀ᵐ ω ∂G.law p,
      1 ≤ G.adjustedCeilingBandCount a c (l-u) (u-l) ω x ∧
        G.adjustedCeilingBandCount a c (l-u) (u-l) ω x ≠ ⊤)
    (L Q : ℝ≥0∞)
    (hL : (∫⁻ ω, (G.adjustedCeilingBandCount a c (l-u) (u-l) ω x)^α ∂G.law p) ≤ L)
    (hQ : ∀ r ∈ O.roots, (∫⁻ ω,
      (G.adjustedCeilingBandCount a (c-u) (-u) (-l) ω r)^(1-δ) ∂G.law p) ≤ Q) :
    (∫⁻ ω, (G.adjustedCeilingBandCount a (c-(u-l)) l u ω x)^α ∂G.law p) ≤
      (((ENNReal.ofReal m)⁻¹*ENNReal.ofReal (Real.exp (-l))*
        (∑ r ∈ O.roots, ENNReal.ofReal (a r)))*Q)^α * L^δ := by
  let B (ω : Set E) (z : V) := G.adjustedCeilingBandCount a (c-(u-l)) l u ω z *
    (G.adjustedCeilingBandCount a c (l-u) (u-l) ω z)^(-δ)
  have hroot : ENNReal.ofReal m*(∫⁻ ω, B ω x ∂G.law p) ≤
      ∑ r ∈ O.roots, ENNReal.ofReal (a r)*(∫⁻ ω, B ω r ∂G.law p) := by
    obtain ⟨r,hr,φ,rfl⟩ := O.cover x
    change ENNReal.ofReal m*(∫⁻ ω,
      G.adjustedCeilingBandCount a (c-(u-l)) l u ω (φ.vertex r) *
        (G.adjustedCeilingBandCount a c (l-u) (u-l) ω (φ.vertex r))^(-δ) ∂G.law p) ≤ _
    rw [G.expected_band_product_aut a ha c l u δ φ p r]
    exact (mul_le_mul' (ENNReal.ofReal_le_ofReal (ham r)) le_rfl).trans
      (Finset.single_le_sum (f := fun r => ENNReal.ofReal (a r)*(∫⁻ ω, B ω r ∂G.law p))
        (fun _ _ => bot_le) hr)
  have hδ1 : δ < 1 := by linarith
  have hprod : (∫⁻ ω, B ω x ∂G.law p) ≤
      ((ENNReal.ofReal m)⁻¹*ENNReal.ofReal (Real.exp (-l))*
        (∑ r ∈ O.roots, ENNReal.ofReal (a r)))*Q := by
    have hqsum : (∑ r ∈ O.roots, ENNReal.ofReal (a r)*(∫⁻ ω,
        (G.adjustedCeilingBandCount a (c-u) (-u) (-l) ω r)^(1-δ) ∂G.law p)) ≤
        (∑ r ∈ O.roots, ENNReal.ofReal (a r))*Q := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun r hr => mul_le_mul' le_rfl (hQ r hr)
    have hh := hroot.trans ((G.expected_fractional_band_transport O hc hl a hapos ha p c l u hδ hδ1).trans
      (mul_le_mul' le_rfl hqsum))
    calc
      _ = (ENNReal.ofReal m)⁻¹*(ENNReal.ofReal m*(∫⁻ ω, B ω x ∂G.law p)) := by
        rw [←mul_assoc,ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr hm))
          ENNReal.ofReal_ne_top,one_mul]
      _ ≤ _ := (mul_le_mul' le_rfl hh).trans_eq (by ring)
  exact (fractional_holder_with_count (G.law p)
    (fun ω => G.adjustedCeilingBandCount a (c-(u-l)) l u ω x)
    (fun ω => G.adjustedCeilingBandCount a c (l-u) (u-l) ω x)
    (G.measurable_adjustedCeilingBandCount a _ _ _ x)
    (G.measurable_adjustedCeilingBandCount a _ _ _ x) hZfin hα hα1 hδ hδα).trans
      (mul_le_mul' (ENNReal.rpow_le_rpow hprod hα.le) (ENNReal.rpow_le_rpow hL hδ))

end CriticalPercolation.BondGraph

end

end OAI
