import Mathlib
import OAI.Probability.CriticalPercolation.Modular.OrbitalMassTransport
import OAI.Probability.CriticalPercolation.Modular.UnimodularUnique

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def CombinatoriallyUnimodular.unimodularRoot (hu : G.CombinatoriallyUnimodular)
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (o : V) : G.UnimodularRoot := by
  let R := G.orbitRepresentatives hq
  let Z := ∑ x ∈ R.roots, G.modularRatio o x
  have hZ : 0 < Z := by
    obtain ⟨u,hu,_,_⟩ := R.cover o
    exact Finset.sum_pos' (fun x _ => (G.modularRatio_pos hc hl o x).le)
      ⟨u,hu,G.modularRatio_pos hc hl o u⟩
  let w := fun x => G.modularRatio o x / Z
  have hw (φ : G.Aut) (x : V) : w (φ.vertex x) = w x := by
    simp only [w,CombinatoriallyUnimodular.rootWeight_invariant G hu hc hl]
  have hbal (x y : V) : w x * (G.suborbitCard x y : ℝ) = w y * (G.suborbitCard y x : ℝ) := by
    simp only [w,div_mul_eq_mul_div]
    rw [G.modularRatio_card_balance hc hl]
  refine ⟨R.roots,w,?_,?_,R.cover,?_⟩
  · intro x _
    exact div_pos (G.modularRatio_pos hc hl o x) hZ
  · change (∑ x ∈ R.roots, G.modularRatio o x / Z) = 1
    rw [←Finset.sum_div,div_self (ne_of_gt hZ)]
  · exact OrbitRepresentatives.massTransport G R hc hl w hw hbal

theorem CombinatoriallyUnimodular.critical_atMostOneInfinite_ae
    (hu : G.CombinatoriallyUnimodular) (hc : G.fullGraph.Connected)
    (hl : G.LocallyFinite) (hq : G.QuasiTransitive) (hpc : G.criticalProbability < 1)
    (o : V) : ∀ᵐ ω ∂G.law G.criticalProbability, ω ∈ G.atMostOneInfinite := by
  let := G.countable_vertices hc hl
  let := G.countable_bonds hc hl
  exact UnimodularRoot.critical_atMostOneInfinite_ae G
    (CombinatoriallyUnimodular.unimodularRoot G hu hc hl hq o) hc hl hpc

theorem CombinatoriallyUnimodular.exponential_critical_null
    (hu : G.CombinatoriallyUnimodular) (hc : G.fullGraph.Connected)
    (hl : G.LocallyFinite) (hq : G.QuasiTransitive) (hpc : G.criticalProbability < 1)
    (o : V) (γ : ℝ) (hγ : 0 < γ) (N : ℕ)
    (hgrowth : ∀ m≥N, ∀ v : V, γ*m ≤ Real.log ((G.vertexBall v m).ncard : ℝ)) :
    G.law G.criticalProbability G.percolates = 0 :=
  UnimodularRoot.exponential_critical_null G
    (CombinatoriallyUnimodular.unimodularRoot G hu hc hl hq o) hc hl hpc o γ hγ N hgrowth

end CriticalPercolation.BondGraph
end
end

end OAI
