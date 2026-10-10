import OAI.Probability.BenjaminiSchramm.FirstHeightPeakWalk
import OAI.Probability.BenjaminiSchramm.FiniteEnergyObservable

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem fractional_slab_root_ascent
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (a : V → ℝ)
    (p : unitInterval) (k r c B : ℝ) (hk : 0 ≤ k) (hr : 0 ≤ r)
    {x y : V} (w : G.fullGraph.Walk x y)
    (hcy : c ≤ G.orbitAdjustedHeight a x y)
    (hw : ∀ v ∈ w.support, 0 ≤ G.orbitAdjustedHeight a x v ∧
      G.orbitAdjustedHeight a x v ≤ G.orbitAdjustedHeight a x y)
    {q : ℝ} (hq : 0 ≤ q) :
    ENNReal.ofReal ((min (p : ℝ) (1-p))^w.length)*
      (∫⁻ ω, (restrictedLayerCount G.ends
        (Percolation.internalEdges G.ends {z | -k-r ≤ G.orbitAdjustedHeight a x z ∧ G.orbitAdjustedHeight a x z ≤ c})
        {z | -k-B ≤ G.orbitAdjustedHeight a x z ∧ G.orbitAdjustedHeight a x z ≤ -k+B} ω x)^q ∂G.law p) ≤
      ∫⁻ ω, (restrictedLayerCount G.ends
        (Percolation.internalEdges G.ends {z | -(k+G.orbitAdjustedHeight a x y)-r ≤ G.orbitAdjustedHeight a y z ∧
          G.orbitAdjustedHeight a y z ≤ 0})
        {z | -(k+G.orbitAdjustedHeight a x y)-B ≤ G.orbitAdjustedHeight a y z ∧
          G.orbitAdjustedHeight a y z ≤ -(k+G.orbitAdjustedHeight a x y)+B} ω y)^q ∂G.law p := by
  let h := G.orbitAdjustedHeight a x y
  let I := Percolation.internalEdges G.ends {z | -k-r ≤ G.orbitAdjustedHeight a x z ∧ G.orbitAdjustedHeight a x z ≤ c}
  let J := Percolation.internalEdges G.ends {z | -(k+h)-r ≤ G.orbitAdjustedHeight a y z ∧ G.orbitAdjustedHeight a y z ≤ 0}
  let W : Set V := {z | -k-B ≤ G.orbitAdjustedHeight a x z ∧ G.orbitAdjustedHeight a x z ≤ -k+B}
  let Z : Set V := {z | -(k+h)-B ≤ G.orbitAdjustedHeight a y z ∧ G.orbitAdjustedHeight a y z ≤ -(k+h)+B}
  have hIJ : I ⊆ J := Percolation.internalEdges_mono G.ends (by
    intro z hz
    have hh := G.orbitAdjustedHeight_change_base hc hl a x y z
    exact ⟨by dsimp [h]; linarith [hz.1],by linarith [hz.2]⟩)
  have hWZ : W ⊆ Z := by
    intro z hz
    have hh := G.orbitAdjustedHeight_change_base hc hl a x y z
    exact ⟨by dsimp [h]; linarith [hz.1],by dsimp [h]; linarith [hz.2]⟩
  let f : G.fullGraph →g Percolation.openSimpleGraph G.ends Set.univ :=
    ⟨id,fun {_ _} h => by
      rw [←criticalModel_openGraph G.ends Set.univ]
      exact h⟩
  obtain ⟨F,hF,hconn⟩ := walk_finite_open_restriction G.ends (w.reverse.map f)
    {z | -(k+h)-r ≤ G.orbitAdjustedHeight a y z ∧ G.orbitAdjustedHeight a y z ≤ 0} (by
      intro z hz
      have hz' : z ∈ w.support := by
        rw [SimpleGraph.Walk.support_map] at hz
        change z ∈ w.reverse.support.map id at hz
        simpa only [List.map_id_fun,id_eq,SimpleGraph.Walk.support_reverse,List.mem_reverse] using hz
      have hh := G.orbitAdjustedHeight_change_base hc hl a x y z
      exact ⟨by dsimp [h]; linarith [(hw z hz').1],by linarith [(hw z hz').2]⟩)
  have hlen : F.card ≤ w.length := by
    simpa only [SimpleGraph.Walk.length_map,SimpleGraph.Walk.length_reverse] using hF
  have hcost : ENNReal.ofReal ((min (p : ℝ) (1-p))^w.length) ≤
      ENNReal.ofReal ((min (p : ℝ) (1-p))^F.card) := by
    apply ENNReal.ofReal_le_ofReal
    exact pow_le_pow_of_le_one (le_min p.2.1 (sub_nonneg.mpr p.2.2))
      ((min_le_left _ _).trans p.2.2) hlen
  exact (mul_le_mul' hcost le_rfl).trans
    (forced_path_fractional_layer_comparison G.ends p F I J W Z hIJ hWZ y x hconn hq)

end CriticalPercolation.BondGraph

end

end OAI
