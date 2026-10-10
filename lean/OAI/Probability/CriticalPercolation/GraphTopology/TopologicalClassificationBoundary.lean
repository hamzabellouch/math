import Mathlib
import OAI.Probability.CriticalPercolation.Model
import OAI.Probability.CriticalPercolation.Classification.FaithfulOrbitalModel
import OAI.Probability.CriticalPercolation.Criticality.MainSparseBoundary
import OAI.Probability.CriticalPercolation.GraphGeometry.FullOrbitalStructureTransfer
import OAI.Probability.CriticalPercolation.GraphTopology.GraphGeneratingNeighborhood

namespace OAI

section
noncomputable section
open Set Function MeasureTheory Topology
open scoped Classical ENNReal Pointwise

namespace CriticalPercolation
namespace GraphTopology
variable {X : Type*} (Γ : SimpleGraph X)

def HasCompactOpenVirtuallyNilpotentQuotient : Prop :=
  let _ : TopologicalSpace X := ⊥
  let _ : TopologicalSpace (Γ ≃g Γ) := autTopology Γ
  ∃ H : Subgroup (Γ ≃g Γ), ∃ hn : H.Normal,
    let _ := hn
    IsCompact (H : Set (Γ ≃g Γ)) ∧ IsOpen (H : Set (Γ ≃g Γ)) ∧
      ∃ N : Subgroup ((Γ ≃g Γ) ⧸ H), Group.IsNilpotent N ∧ N.index≠0

def HasUniformCompactApproximatePowers (K : ℝ) : Prop :=
  let _ : TopologicalSpace X := ⊥
  let _ : TopologicalSpace (Γ ≃g Γ) := autTopology Γ
  ∃ S : Set (Γ ≃g Γ), IsCompact S ∧ IsOpen S ∧ (1 : Γ ≃g Γ)∈S ∧
    S⁻¹=S ∧ Subgroup.closure S=⊤ ∧
    ∀ R : ℕ, ∃ n≥R, IsCompact (S^n) ∧ IsOpen (S^n) ∧
      IsApproximateSubgroup K (S^n)

lemma uniform_compact_approximate_powers_of_sparse_polynomial
    (hc : Γ.Connected) (hl : ∀ x, (Γ.neighborSet x).Finite)
    (ht : ∀ u v, ∃ g : Γ ≃g Γ, g u=v) (o : X) (d : ℕ)
    (hpoly : ∀ R : ℕ, ∃ n≥R, (reachBall Γ o n).ncard≤n^d) :
    HasUniformCompactApproximatePowers Γ (5^(d+1)) := by
  let _ : TopologicalSpace X := ⊥
  let _ : DiscreteTopology X := ⟨rfl⟩
  let _ : TopologicalSpace (Γ ≃g Γ) := autTopology Γ
  exact ⟨displacement Γ o 1,
    compact_open_generating_approximate_powers Γ hc hl ht o d hpoly⟩

end GraphTopology
namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

theorem main_failure_topological_classification_counterexample [Infinite V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (hpc : G.criticalProbability<1)
    (hper : G.law G.criticalProbability G.percolates≠0) (o : V) :
    ∃ d : ℕ, 2≤d ∧ ∃ C : ℕ,
      (G.orbitPower o (2*C+1)).Connected ∧
      (MulAction.orbit G.Aut o).Infinite ∧
      (∀ u, ((G.orbitPower o (2*C+1)).neighborSet u).Finite) ∧
      (∀ u v, ∃ g : G.orbitPower o (2*C+1) ≃g G.orbitPower o (2*C+1), g u=v) ∧
      (∀ R : ℕ, ∃ n≥R, ∀ u : MulAction.orbit G.Aut o,
        (GraphTopology.reachBall (G.orbitPower o (2*C+1)) u n).ncard≤n^(d+1)) ∧
      GraphTopology.HasUniformCompactApproximatePowers
        (G.orbitPower o (2*C+1)) (5^(d+2)) ∧
      ¬GraphTopology.HasCompactOpenVirtuallyNilpotentQuotient
        (G.orbitPower o (2*C+1)) := by
  obtain ⟨hg,_,d,hd,hpoly⟩ := G.main_failure_sparse_polynomial hc hl hq hpc hper
  obtain ⟨C,Λ,hfg,hconn,hinf,hloc,htrans,hker,hreps,hscales⟩ :=
    G.sparse_polynomial_faithful_orbital_model hc hl hq o d hpoly
  let _ : Group.FG Λ := hfg
  have ht : ∀ u v, ∃ g : G.orbitPower o (2*C+1) ≃g G.orbitPower o (2*C+1), g u=v := by
    intro u v
    obtain ⟨g,hg⟩ := htrans u v
    exact ⟨g.val,hg⟩
  have hpow : GraphTopology.HasUniformCompactApproximatePowers
      (G.orbitPower o (2*C+1)) (5^(d+2)) := by
    apply GraphTopology.uniform_compact_approximate_powers_of_sparse_polynomial
      _ hconn hloc ht (⟨o,MulAction.mem_orbit_self o⟩ : MulAction.orbit G.Aut o) (d+1)
    intro R
    obtain ⟨n,hn,hh⟩ := hscales R
    exact ⟨n,hn,hh _⟩
  refine ⟨d,hd,C,hconn,hinf,hloc,ht,hscales,hpow,?_⟩
  rintro ⟨H,hn,hcomp,hopen,N,hnil,hN⟩
  let _ := hn
  let _ := hnil
  obtain ⟨S,hS,hcover⟩ := hreps
  exact hper (G.critical_null_of_compact_open_orbital_quotient hc hl hg o (2*C+1)
    hconn Λ S hS hcover H N hN ⟨hcomp,hopen⟩ hpc)

end BondGraph
end CriticalPercolation
end
end

end OAI
