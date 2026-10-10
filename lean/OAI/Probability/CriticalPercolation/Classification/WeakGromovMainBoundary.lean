import Mathlib
import OAI.Probability.CriticalPercolation.Classification.RawClassificationBoundary
import OAI.Probability.CriticalPercolation.GraphGeometry.GraphQuotientPolynomial

namespace OAI

section
noncomputable section
open Set Function Topology

namespace CriticalPercolation
namespace GraphTopology
variable {X : Type*} (Γ : SimpleGraph X)

def HasWeakGromovQuotientCounterexample : Prop :=
  let _ : TopologicalSpace X := ⊥
  let _ : TopologicalSpace (Γ ≃g Γ) := autTopology Γ
  ∃ H : Subgroup (Γ ≃g Γ), ∃ hn : H.Normal, let _ := hn
    IsCompact (H : Set (Γ ≃g Γ)) ∧ IsOpen (H : Set (Γ ≃g Γ)) ∧
    Group.FG ((Γ ≃g Γ) ⧸ H) ∧
    CompactQuotient.HasSparsePolynomialWordGrowth ((Γ ≃g Γ) ⧸ H) ∧
    ¬Group.IsVirtuallyNilpotent ((Γ ≃g Γ) ⧸ H)

end GraphTopology
namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

theorem main_failure_raw_Carolino_or_weak_Gromov [Infinite V]
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
      ((¬(let _ : TopologicalSpace (MulAction.orbit G.Aut o) := ⊥
          let _ : TopologicalSpace (G.orbitPower o (2*C+1) ≃g G.orbitPower o (2*C+1)) :=
            GraphTopology.autTopology (G.orbitPower o (2*C+1))
          CompactQuotient.HasUniformCompactLocallyConnectedModels
            (G.orbitPower o (2*C+1) ≃g G.orbitPower o (2*C+1)) (5^(d+2)))) ∨
        GraphTopology.HasWeakGromovQuotientCounterexample (G.orbitPower o (2*C+1))) := by
  obtain ⟨d,hd,C,hconn,hinf,hloc,ht,hpoly,hpow,hfail⟩ :=
    G.main_failure_raw_Carolino_or_finite_BGT hc hl hq hpc hper o
  refine ⟨d,hd,C,hconn,hinf,hloc,ht,hpoly,hpow,?_⟩
  rcases hfail with hcar | hfin
  · exact Or.inl hcar
  · right
    let u : MulAction.orbit G.Aut o := ⟨o,MulAction.mem_orbit_self o⟩
    exact GraphTopology.weak_Gromov_counterexample_of_finite_classification_failure
      _ hconn hloc ht u (d+1) (fun R => by
        obtain ⟨n,hn,hp⟩ := hpoly R
        exact ⟨n,hn,hp u⟩) hfin

end BondGraph
end CriticalPercolation
end
end

end OAI
