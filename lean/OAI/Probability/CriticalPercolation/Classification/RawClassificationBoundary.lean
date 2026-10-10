import Mathlib
import OAI.Probability.CriticalPercolation.Classification.ClassificationProducerBoundary
import OAI.Probability.CriticalPercolation.GraphGeometry.SubgroupOrbitKernel
import OAI.Probability.CriticalPercolation.Growth.CosetBallIndex

namespace OAI

section
noncomputable section
open Set Function Topology
open scoped Pointwise

namespace CriticalPercolation
namespace CompactQuotient

def HasUniformCompactLocallyConnectedModels (A : Type*) [Group A]
    [TopologicalSpace A] (K : ℝ) : Prop :=
  ∃ B : ℕ, ∀ U : Set A, IsOpen U → IsCompact U → IsApproximateSubgroup K U →
    ∃ L : Subgroup A, ∃ H : Subgroup L, ∃ hn : H.Normal, let _ := hn
      IsCompact (H : Set L) ∧
      ((Subtype.val : L → A) '' (H : Set L)⊆U^4) ∧
      LocallyCompactSpace (L ⧸ H) ∧ LocallyConnectedSpace (L ⧸ H) ∧
      ∃ F : Finset A, F.card≤B ∧ U⊆(F : Set A)*(L : Set A)

end CompactQuotient
namespace GraphTopology
variable {X : Type*} (Γ : SimpleGraph X)

theorem compact_open_normal_of_raw_models {K : ℝ}
    (hpow : HasUniformCompactApproximatePowers Γ K)
    (hcar : let _ : TopologicalSpace X := ⊥
      let _ : TopologicalSpace (Γ ≃g Γ) := autTopology Γ
      CompactQuotient.HasUniformCompactLocallyConnectedModels (Γ ≃g Γ) K) :
    let _ : TopologicalSpace X := ⊥
    let _ : TopologicalSpace (Γ ≃g Γ) := autTopology Γ
    ∃ J : Subgroup (Γ ≃g Γ), J.Normal ∧
      IsCompact (J : Set (Γ ≃g Γ)) ∧ IsOpen (J : Set (Γ ≃g Γ)) := by
  let _ : TopologicalSpace X := ⊥
  let _ : DiscreteTopology X := ⟨rfl⟩
  let _ : TopologicalSpace (Γ ≃g Γ) := autTopology Γ
  obtain ⟨S,hSc,hSo,h1,hinv,hgen,hscales⟩ := hpow
  obtain ⟨B,hB⟩ := hcar
  obtain ⟨n,hn,hcomp,hopen,happrox⟩ := hscales B
  obtain ⟨L,H,hHN,hH,_,hLC,hConn,F,hF,hcover⟩ := hB (S^n) hopen hcomp happrox
  let _ := hHN
  let _ := hLC
  let _ := hConn
  let _ : L.FiniteIndex := CosetGrowth.finiteIndex_of_few_cosets S L h1 hinv hgen
    n F (hF.trans hn) hcover
  exact compact_open_normal_of_finiteIndex_subquotient Γ L H hH

theorem raw_classification_failure_dichotomy {K : ℝ}
    (hpow : HasUniformCompactApproximatePowers Γ K)
    (hfail : ¬HasCompactOpenVirtuallyNilpotentQuotient Γ) :
    (¬(let _ : TopologicalSpace X := ⊥
      let _ : TopologicalSpace (Γ ≃g Γ) := autTopology Γ
      CompactQuotient.HasUniformCompactLocallyConnectedModels (Γ ≃g Γ) K)) ∨
      HasFiniteApproximateQuotientCounterexample Γ K := by
  let _ : TopologicalSpace X := ⊥
  let _ : DiscreteTopology X := ⟨rfl⟩
  let _ : TopologicalSpace (Γ ≃g Γ) := autTopology Γ
  by_cases hc : CompactQuotient.HasUniformCompactLocallyConnectedModels (Γ ≃g Γ) K
  · right
    obtain ⟨J,hn,hJc,hJo⟩ := compact_open_normal_of_raw_models Γ hpow hc
    let _ := hn
    obtain ⟨S,hS,_,h1,hinv,hgen,hscales⟩ := hpow
    have hfin : CompactQuotient.UniformFiniteApproximatePowers ((Γ ≃g Γ) ⧸ J) K := by
      apply CompactQuotient.finite_generating_approximate_powers J hJo K S hS h1 hinv hgen
      intro R
      obtain ⟨n,hn,_,_,ha⟩ := hscales R
      exact ⟨n,hn,ha⟩
    refine ⟨J,hn,hJc,hJo,CompactQuotient.fg_of_uniformFiniteApproximatePowers hfin,hfin,?_⟩
    rintro ⟨F,hFN,hF,N,hNil,hN⟩
    let _ := hFN
    let _ := hNil
    exact hfail (CompactQuotient.lift_finite_by_virtually_nilpotent J hJc hJo F hF N hN)
  · exact Or.inl hc

end GraphTopology
namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

theorem main_failure_raw_Carolino_or_finite_BGT [Infinite V]
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
        GraphTopology.HasFiniteApproximateQuotientCounterexample
          (G.orbitPower o (2*C+1)) (5^(d+2))) := by
  obtain ⟨d,hd,C,hconn,hinf,hloc,ht,hpoly,hpow,hfail⟩ :=
    G.main_failure_topological_classification_counterexample hc hl hq hpc hper o
  exact ⟨d,hd,C,hconn,hinf,hloc,ht,hpoly,hpow,
    GraphTopology.raw_classification_failure_dichotomy _ hpow hfail⟩

end BondGraph
end CriticalPercolation
end
end

end OAI
