import OAI.Probability.BenjaminiSchramm.BoundedLayerShift

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

lemma measurable_adjustedCeilingBandCount (a : V → ℝ) (c l u : ℝ) (x : V) :
    Measurable (fun ω => G.adjustedCeilingBandCount a c l u ω x) :=
  Measurable.tsum fun y => G.measurable_adjustedCeilingBandTransport a c l u x y

omit [Countable V] [Countable E] in
lemma adjustedCeilingBandCount_aut (a : V → ℝ)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x) (c l u : ℝ)
    (φ : G.Aut) (ω : Set E) (x : V) :
    G.adjustedCeilingBandCount a c l u (φ.edge '' ω) (φ.vertex x) =
      G.adjustedCeilingBandCount a c l u ω x := by
  unfold adjustedCeilingBandCount
  rw [←φ.vertex.tsum_eq]
  simp only [G.adjustedCeilingBandTransport_aut a ha c l u]

lemma expected_adjustedCeilingBandCount_aut (a : V → ℝ)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x) (c l u : ℝ)
    (φ : G.Aut) (p : unitInterval) (x : V) :
    (∫⁻ ω, G.adjustedCeilingBandCount a c l u ω (φ.vertex x) ∂G.law p) =
      ∫⁻ ω, G.adjustedCeilingBandCount a c l u ω x ∂G.law p := by
  conv_lhs => rw [←G.law_map_aut p φ]
  rw [lintegral_map (G.measurable_adjustedCeilingBandCount a c l u _)
    (BernoulliProduct.measurable_image_equiv φ.edge)]
  simp only [G.adjustedCeilingBandCount_aut a ha c l u]

theorem expected_ceilingBandCount_uniform_bound
    (O : G.OrbitRepresentatives) (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (hapos : ∀ x, 0 < a x)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x)
    (m : ℝ) (hm : 0 < m) (ham : ∀ x, m ≤ a x)
    (p : unitInterval) (c l u : ℝ) (x : V) :
    (∫⁻ ω, G.adjustedCeilingBandCount a c l u ω x ∂G.law p) ≤
      ((ENNReal.ofReal m)⁻¹*(∑ r ∈ O.roots, ENNReal.ofReal (a r)))*
        ENNReal.ofReal (Real.exp (-l))*
          (⨆ y, ∫⁻ ω, G.adjustedCeilingBandCount a (c-l) (-u) (-l) ω y ∂G.law p) := by
  have hroot : ENNReal.ofReal m*
      (∫⁻ ω, G.adjustedCeilingBandCount a c l u ω x ∂G.law p) ≤
      ∑ r ∈ O.roots, ENNReal.ofReal (a r)*
        (∫⁻ ω, G.adjustedCeilingBandCount a c l u ω r ∂G.law p) := by
    obtain ⟨r,hr,φ,rfl⟩ := O.cover x
    rw [G.expected_adjustedCeilingBandCount_aut a ha c l u φ p r]
    exact (mul_le_mul' (ENNReal.ofReal_le_ofReal (ham r)) le_rfl).trans
      (Finset.single_le_sum (f := fun r => ENNReal.ofReal (a r)*
        (∫⁻ ω, G.adjustedCeilingBandCount a c l u ω r ∂G.law p))
        (fun _ _ => bot_le) hr)
  have hsum : (∑ r ∈ O.roots, ENNReal.ofReal (a r)*
      (∫⁻ ω, G.adjustedCeilingBandCount a (c-l) (-u) (-l) ω r ∂G.law p)) ≤
      (∑ r ∈ O.roots, ENNReal.ofReal (a r))*
        (⨆ y, ∫⁻ ω, G.adjustedCeilingBandCount a (c-l) (-u) (-l) ω y ∂G.law p) := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun r _ => mul_le_mul' le_rfl
      (le_iSup (fun y => ∫⁻ ω, G.adjustedCeilingBandCount a (c-l) (-u) (-l) ω y ∂G.law p) r)
  have hh := hroot.trans ((G.expected_adjustedCeilingBandCount_reciprocity
    O hc hl a hapos ha p c l u).2.trans (mul_le_mul' le_rfl hsum))
  calc
    _ = (ENNReal.ofReal m)⁻¹*(ENNReal.ofReal m*
        (∫⁻ ω, G.adjustedCeilingBandCount a c l u ω x ∂G.law p)) := by
      rw [←mul_assoc,ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr hm))
        ENNReal.ofReal_ne_top,one_mul]
    _ ≤ _ := (mul_le_mul' le_rfl hh).trans_eq (by ring)

end CriticalPercolation.BondGraph

end

end OAI
