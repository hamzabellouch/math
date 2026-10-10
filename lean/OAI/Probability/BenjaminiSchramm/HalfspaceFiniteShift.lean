import OAI.Probability.BenjaminiSchramm.CeilingDownCrudeProfile

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

lemma walk_fractional_layer_comparison (p : unitInterval) (I : Set E)
    (D W Z : Set V) (hI : I ⊆ Percolation.internalEdges G.ends D) (hW : W ⊆ Z)
    {x y : V} (w : G.fullGraph.Walk x y) (hw : ∀ v ∈ w.support, v ∈ D)
    {q : ℝ} (hq : 0 ≤ q) :
    ENNReal.ofReal ((min (p : ℝ) (1-p))^w.length)*
      (∫⁻ ω, (restrictedLayerCount G.ends I W ω y)^q ∂G.law p) ≤
        ∫⁻ ω, (restrictedLayerCount G.ends (Percolation.internalEdges G.ends D) Z ω x)^q ∂G.law p := by
  let f : G.fullGraph →g Percolation.openSimpleGraph G.ends Set.univ :=
    ⟨id,fun {_ _} h => by rw [←criticalModel_openGraph G.ends Set.univ]; exact h⟩
  obtain ⟨F,hF,hconn⟩ := walk_finite_open_restriction G.ends (w.map f) D (by
    intro v hv
    rw [SimpleGraph.Walk.support_map] at hv
    have hv' : v ∈ w.support := by
      change v ∈ w.support.map id at hv
      simpa only [List.map_id_fun,id_eq] using hv
    exact hw v hv')
  have hcard : F.card ≤ w.length := by simpa only [SimpleGraph.Walk.length_map] using hF
  have hcost : ENNReal.ofReal ((min (p : ℝ) (1-p))^w.length) ≤
      ENNReal.ofReal ((min (p : ℝ) (1-p))^F.card) := by
    apply ENNReal.ofReal_le_ofReal
    exact pow_le_pow_of_le_one (le_min p.2.1 (sub_nonneg.mpr p.2.2))
      ((min_le_left _ _).trans p.2.2) hcard
  exact (mul_le_mul' hcost le_rfl).trans
    (forced_path_fractional_layer_comparison G.ends p F I _ W Z hI hW x y hconn hq)

theorem fractional_ceiling_root_ascent
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (a : V → ℝ)
    (p : unitInterval) (k c B : ℝ) {x y : V} (w : G.fullGraph.Walk x y)
    (hcy : c ≤ G.orbitAdjustedHeight a x y)
    (hw : ∀ v ∈ w.support, G.orbitAdjustedHeight a x v ≤ G.orbitAdjustedHeight a x y)
    {q : ℝ} (hq : 0 ≤ q) :
    ENNReal.ofReal ((min (p : ℝ) (1-p))^w.length)*
      (∫⁻ ω, (restrictedLayerCount G.ends
        (Percolation.internalEdges G.ends {v | G.orbitAdjustedHeight a x v ≤ c})
        {v | -k-B ≤ G.orbitAdjustedHeight a x v ∧ G.orbitAdjustedHeight a x v ≤ -k+B} ω x)^q ∂G.law p) ≤
      ∫⁻ ω, (restrictedLayerCount G.ends
        (Percolation.internalEdges G.ends {v | G.orbitAdjustedHeight a y v ≤ 0})
        {v | -(k+G.orbitAdjustedHeight a x y)-B ≤ G.orbitAdjustedHeight a y v ∧
          G.orbitAdjustedHeight a y v ≤ -(k+G.orbitAdjustedHeight a x y)+B} ω y)^q ∂G.law p := by
  rw [←SimpleGraph.Walk.length_reverse w]
  apply G.walk_fractional_layer_comparison p _ _ _ _ _ _ w.reverse _ hq
  · apply Percolation.internalEdges_mono G.ends
    intro v hv
    have hh := G.orbitAdjustedHeight_change_base hc hl a x y v
    change G.orbitAdjustedHeight a x v ≤ c at hv
    change G.orbitAdjustedHeight a y v ≤ 0
    linarith
  · intro v hv
    have hh := G.orbitAdjustedHeight_change_base hc hl a x y v
    exact ⟨by linarith [hv.1],by linarith [hv.2]⟩
  · intro v hv
    have hv' : v ∈ w.support := by simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hv
    have hh := G.orbitAdjustedHeight_change_base hc hl a x y v
    change G.orbitAdjustedHeight a y v ≤ 0
    linarith [hw v hv']

theorem fractional_floor_root_descent
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (a : V → ℝ)
    (p : unitInterval) (k c B : ℝ) {x y : V} (w : G.fullGraph.Walk x y)
    (hcy : G.orbitAdjustedHeight a x y ≤ -c)
    (hw : ∀ v ∈ w.support, G.orbitAdjustedHeight a x y ≤ G.orbitAdjustedHeight a x v)
    {q : ℝ} (hq : 0 ≤ q) :
    ENNReal.ofReal ((min (p : ℝ) (1-p))^w.length)*
      (∫⁻ ω, (restrictedLayerCount G.ends
        (Percolation.internalEdges G.ends {v | -c ≤ G.orbitAdjustedHeight a x v})
        {v | k-B ≤ G.orbitAdjustedHeight a x v ∧ G.orbitAdjustedHeight a x v ≤ k+B} ω x)^q ∂G.law p) ≤
      ∫⁻ ω, (restrictedLayerCount G.ends
        (Percolation.internalEdges G.ends {v | 0 ≤ G.orbitAdjustedHeight a y v})
        {v | (k-G.orbitAdjustedHeight a x y)-B ≤ G.orbitAdjustedHeight a y v ∧
          G.orbitAdjustedHeight a y v ≤ (k-G.orbitAdjustedHeight a x y)+B} ω y)^q ∂G.law p := by
  rw [←SimpleGraph.Walk.length_reverse w]
  apply G.walk_fractional_layer_comparison p _ _ _ _ _ _ w.reverse _ hq
  · apply Percolation.internalEdges_mono G.ends
    intro v hv
    have hh := G.orbitAdjustedHeight_change_base hc hl a x y v
    change -c ≤ G.orbitAdjustedHeight a x v at hv
    change 0 ≤ G.orbitAdjustedHeight a y v
    linarith
  · intro v hv
    have hh := G.orbitAdjustedHeight_change_base hc hl a x y v
    exact ⟨by linarith [hv.1],by linarith [hv.2]⟩
  · intro v hv
    have hv' : v ∈ w.support := by simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hv
    have hh := G.orbitAdjustedHeight_change_base hc hl a x y v
    change 0 ≤ G.orbitAdjustedHeight a y v
    linarith [hw v hv']

end CriticalPercolation.BondGraph

end

end OAI
