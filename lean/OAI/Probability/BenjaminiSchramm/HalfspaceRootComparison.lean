import OAI.Probability.BenjaminiSchramm.NormalizedCrossingRate

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma walk_finite_open_restriction {x y : V} (w : (openSimpleGraph G Set.univ).Walk x y)
    (D : Set V) (hD : ∀ v ∈ w.support, v ∈ D) :
    ∃ s : Finset E, s.card ≤ w.length ∧ ∀ ω : Set E, (s : Set E) ⊆ ω →
      Conn G (ω ∩ internalEdges G D) x y := by
  obtain ⟨l,hl,he,_ho⟩ := walk_lift_bonds G Set.univ w
  have hlen : l.length = w.length := by
    simpa only [List.length_map,SimpleGraph.Walk.length_edges] using congrArg List.length he
  refine ⟨l.toFinset,(List.toFinset_card_le l).trans_eq hlen,fun ω hω => ?_⟩
  apply hl.conn
  intro e he'
  refine ⟨hω (List.mem_toFinset.mpr he'),?_⟩
  intro v hv
  exact hD v (SimpleGraph.Walk.mem_support_of_mem_edges (he ▸ List.mem_map_of_mem he') hv)

end Percolation.BenjaminiSchramm

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

theorem adjustedHalfspaceHit_path_comparison [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (a : V → ℝ)
    (p : unitInterval) {x y : V} (w : G.fullGraph.Walk x y) (r t : ℝ) (hr : 0 ≤ r)
    (hw : ∀ v ∈ w.support, 0 ≤ G.orbitAdjustedHeight a x v)
    (hxy : r ≤ G.orbitAdjustedHeight a x y) :
    (p : ℝ)^w.length * (G.law p).real (G.adjustedHalfspaceHit a y (-r) t) ≤
      (G.law p).real (G.adjustedHalfspaceHit a x 0 t) := by
  have hg : G.fullGraph = Percolation.openSimpleGraph G.ends Set.univ :=
    criticalModel_openGraph G.ends Set.univ
  let f : G.fullGraph →g Percolation.openSimpleGraph G.ends Set.univ :=
    ⟨id,fun {_ _} h => by simpa only [← hg,id_eq] using h⟩
  obtain ⟨s,hs,hconn⟩ := walk_finite_open_restriction G.ends (w.map f)
    {v | 0 ≤ G.orbitAdjustedHeight a x v} (by
      intro v hv
      have hv' : v ∈ w.support := by
        rw [SimpleGraph.Walk.support_map] at hv
        change v ∈ w.support.map id at hv
        simpa only [List.map_id_fun,id_eq] using hv
      exact hw v hv')
  have hslen : s.card ≤ w.length := by simpa only [SimpleGraph.Walk.length_map] using hs
  let F : Set (Set E) := {ω | (s : Set E) ⊆ ω}
  let B := G.adjustedHalfspaceHit a y (-r) t
  have hF : IsUpperSet F := fun _ _ hωη hω => hω.trans hωη
  have hfF : Percolation.FiniteWitness F := fun _ hω => ⟨s,hω,Set.Subset.rfl⟩
  have hsub : F ∩ B ⊆ G.adjustedHalfspaceHit a x 0 t := by
    rintro ω ⟨hω,⟨z,hz,hyz⟩⟩
    have hyz' : Percolation.Conn G.ends (ω ∩ Percolation.internalEdges G.ends
        {v | 0 ≤ G.orbitAdjustedHeight a x v}) y z := by
      apply Percolation.conn_mono G.ends (Set.inter_subset_inter_right _
        (Percolation.internalEdges_mono G.ends ?_)) hyz
      intro v hv
      change -r ≤ G.orbitAdjustedHeight a y v at hv
      change 0 ≤ G.orbitAdjustedHeight a x v
      rw [G.orbitAdjustedHeight_change_base hc hl a x y v]
      linarith
    refine ⟨z,?_,(hconn ω hω).trans hyz'⟩
    change t ≤ G.orbitAdjustedHeight a x z
    change t ≤ G.orbitAdjustedHeight a y z at hz
    rw [G.orbitAdjustedHeight_change_base hc hl a x y z]
    linarith
  have hassoc := Percolation.association_finiteWitness p F B hF
    (G.adjustedHalfspaceHit_upper a y (-r) t) hfF
    (G.adjustedHalfspaceHit_finiteWitness a y (-r) t)
  have hprob : (G.law p).real F = (p : ℝ)^s.card := Percolation.finite_open_probability p s
  rw [show Percolation.law p = G.law p from rfl, hprob] at hassoc
  apply (le_trans ?_ hassoc).trans (measureReal_mono hsub)
  apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
  exact pow_le_pow_of_le_one p.2.1 p.2.2 hslen

end CriticalPercolation.BondGraph

end

end OAI
