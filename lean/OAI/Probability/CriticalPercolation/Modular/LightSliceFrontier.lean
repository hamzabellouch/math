import Mathlib
import OAI.Probability.CriticalPercolation.Model
import OAI.Probability.CriticalPercolation.Exploration.OpenFrontierDivergence
import OAI.Probability.CriticalPercolation.Exploration.SliceExploration
import OAI.Probability.CriticalPercolation.GraphGeometry.FiniteInduced
import OAI.Probability.CriticalPercolation.Gluing.StripMoves
import OAI.Probability.CriticalPercolation.Modular.ModularClusterMass

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def modularUpperSlice (o : V) (ε : ℝ) : Set V := {x | ε ≤ G.modularRatio x o}

def modularSliceBonds (o : V) (ε : ℝ) : Set E := G.inducedEdges (G.modularUpperSlice o ε)

lemma finite_lightUpperSlice (o v : V) (ε : ℝ) (hε : 0<ε) (ω : Set E)
    (hm : G.modularMass o (G.cluster ω v) ≠ ∞) :
    (G.cluster ω v ∩ G.modularUpperSlice o ε).Finite := by
  apply (ENNReal.finite_const_le_of_tsum_ne_top hm
    (ε := ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε).ne').subset
  intro x hx
  change ENNReal.ofReal ε ≤ if x∈G.cluster ω v then G.stabilizerWeight o x else 0
  rw [ite_eq_left hx.1]
  exact ENNReal.ofReal_le_ofReal hx.2

lemma finite_lightSliceComponent (o v : V) (ε : ℝ) (hε : 0<ε)
    (hv : v∈G.modularUpperSlice o ε) (ω : Set E)
    (hm : G.modularMass o (G.cluster ω v) ≠ ∞) :
    (G.cluster (ω∩G.modularSliceBonds o ε) v).Finite := by
  apply (G.finite_lightUpperSlice o v ε hε ω hm).subset
  intro x hx
  exact ⟨G.cluster_mono Set.inter_subset_left v hx,
    G.cluster_induced_subset ω _ hv hx⟩

lemma modularSliceBonds_exhaust (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o : V) (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0)) :
    ∀ S : Finset E, ∀ᶠ n in atTop, (S : Set E) ⊆ G.modularSliceBonds o (ε n) := by
  have hv (x : V) : ∀ᶠ n in atTop, ε n ≤ G.modularRatio x o :=
    (hε.eventually (gt_mem_nhds (G.modularRatio_pos hc hl x o))).mono (fun _ h => h.le)
  have he (t : Sym2 V) : ∀ᶠ n in atTop, ∀ x∈t, ε n ≤ G.modularRatio x o := by
    refine Sym2.inductionOn t ?_
    intro x y
    filter_upwards [hv x,hv y] with n hn hn'
    intro z hz
    simp only [Sym2.mem_iff] at hz
    rcases hz with rfl|rfl
    · exact hn
    · exact hn'
  intro S
  apply S.eventually_all.mpr
  intro e _
  exact he (G.ends e)

theorem lightSlice_fewOpen_probability_tendsto_zero [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (p : unitInterval) (hp : 0<(p:ℝ)) (hp1 : (p:ℝ)<1) (o v : V)
    (ε : ℕ → ℝ) (hεpos : ∀ n, 0<ε n) (hε : Tendsto ε atTop (𝓝 0)) (N : ℕ) :
    Tendsto (fun n => G.law p (G.lightInfiniteEvent o v ∩
      {ω | (G.freshClusterBoundary (G.modularSliceBonds o (ε n)) v ω ∩ ω).ncard ≤ N}))
      atTop (𝓝 0) := by
  have hlim := G.fewOpenFreshBoundary_probability_tendsto_zero hl p hp hp1
    (fun n => G.modularSliceBonds o (ε n)) (G.modularSliceBonds_exhaust hc hl o ε hε) v N
  have hv : ∀ᶠ n in atTop, v∈G.modularUpperSlice o (ε n) :=
    (hε.eventually (gt_mem_nhds (G.modularRatio_pos hc hl v o))).mono (fun _ h => h.le)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall (fun _ => zero_le))
  filter_upwards [hv] with n hn
  apply measure_mono
  rintro ω ⟨⟨hi,hm⟩,hcount⟩
  exact ⟨hi,G.finite_lightSliceComponent o v (ε n) (hεpos n) hn ω hm.ne,hcount⟩

end CriticalPercolation.BondGraph
end
end

end OAI
