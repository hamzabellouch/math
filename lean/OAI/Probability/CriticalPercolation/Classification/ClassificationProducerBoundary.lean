import Mathlib
import OAI.Probability.CriticalPercolation.Criticality.CompactDiscreteQuotient
import OAI.Probability.CriticalPercolation.GraphTopology.TopologicalClassificationBoundary
import OAI.Probability.CriticalPercolation.GraphTopology.CompactOrbitKernel

namespace OAI

section
noncomputable section
open Set Function Topology
open scoped Classical Pointwise

namespace CriticalPercolation
namespace CompactQuotient

def FiniteByVirtuallyNilpotent (A : Type*) [Group A] : Prop :=
  ∃ F : Subgroup A, ∃ hn : F.Normal, let _ := hn
    (F : Set A).Finite ∧
      ∃ N : Subgroup (A ⧸ F), Group.IsNilpotent N ∧ N.index≠0

def UniformFiniteApproximatePowers (A : Type*) [Group A] (K : ℝ) : Prop :=
  ∃ T : Set A, T.Finite ∧ (1 : A)∈T ∧ T⁻¹=T ∧ Subgroup.closure T=⊤ ∧
    ∀ R : ℕ, ∃ n≥R, IsApproximateSubgroup K (T^n)

lemma fg_of_uniformFiniteApproximatePowers {A : Type*} [Group A] {K : ℝ}
    (h : UniformFiniteApproximatePowers A K) : Group.FG A := by
  obtain ⟨T,hT,_,_,hgen,_⟩ := h
  exact Group.fg_iff.mpr ⟨T,hgen,hT⟩

end CompactQuotient
namespace GraphTopology
variable {X : Type*} (Γ : SimpleGraph X)

def HasCompactNormalOpenLocallyConnectedSubquotient : Prop :=
  let _ : TopologicalSpace X := ⊥
  let _ : TopologicalSpace (Γ ≃g Γ) := autTopology Γ
  ∃ H : Subgroup (Γ ≃g Γ), ∃ hn : H.Normal, let _ := hn
    ∃ L : Subgroup (Γ ≃g Γ), L.Normal ∧ H≤L ∧
      IsCompact (H : Set (Γ ≃g Γ)) ∧ IsOpen (L : Set (Γ ≃g Γ)) ∧ L.index≠0 ∧
        LocallyConnectedSpace (L ⧸ H.subgroupOf L)

def HasFiniteApproximateQuotientCounterexample (K : ℝ) : Prop :=
  let _ : TopologicalSpace X := ⊥
  let _ : TopologicalSpace (Γ ≃g Γ) := autTopology Γ
  ∃ H : Subgroup (Γ ≃g Γ), ∃ hn : H.Normal, let _ := hn
    IsCompact (H : Set (Γ ≃g Γ)) ∧ IsOpen (H : Set (Γ ≃g Γ)) ∧
      Group.FG ((Γ ≃g Γ) ⧸ H) ∧
      CompactQuotient.UniformFiniteApproximatePowers ((Γ ≃g Γ) ⧸ H) K ∧
      ¬CompactQuotient.FiniteByVirtuallyNilpotent ((Γ ≃g Γ) ⧸ H)

theorem classification_failure_dichotomy {K : ℝ}
    (hpow : HasUniformCompactApproximatePowers Γ K)
    (hfail : ¬HasCompactOpenVirtuallyNilpotentQuotient Γ) :
    ¬HasCompactNormalOpenLocallyConnectedSubquotient Γ ∨
      HasFiniteApproximateQuotientCounterexample Γ K := by
  by_cases hcar : HasCompactNormalOpenLocallyConnectedSubquotient Γ
  · right
    let _ : TopologicalSpace X := ⊥
    let _ : DiscreteTopology X := ⟨rfl⟩
    let _ : TopologicalSpace (Γ ≃g Γ) := autTopology Γ
    obtain ⟨H,hn,L,_,_,hH,hL,_,hLC⟩ := hcar
    let _ := hn
    let _ := hLC
    let J := orbitKernel Γ H
    have hJ := compact_open_orbitKernel_of_open_locallyConnected_subquotient Γ H L hH hL
    obtain ⟨S,hS,_,h1,hinv,hgen,hscales⟩ := hpow
    have hfin : CompactQuotient.UniformFiniteApproximatePowers ((Γ ≃g Γ) ⧸ J) K := by
      apply CompactQuotient.finite_generating_approximate_powers J hJ.2 K S hS h1 hinv hgen
      intro R
      obtain ⟨n,hn,_,_,ha⟩ := hscales R
      exact ⟨n,hn,ha⟩
    refine ⟨J,inferInstance,hJ.1,hJ.2,
      CompactQuotient.fg_of_uniformFiniteApproximatePowers hfin,hfin,?_⟩
    rintro ⟨F,hFN,hF,N,hNil,hN⟩
    let _ := hFN
    let _ := hNil
    exact hfail (CompactQuotient.lift_finite_by_virtually_nilpotent J hJ.1 hJ.2 F hF N hN)
  · exact Or.inl hcar

end GraphTopology
namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

theorem main_failure_Carolino_or_finite_BGT [Infinite V]
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
      (¬GraphTopology.HasCompactNormalOpenLocallyConnectedSubquotient
          (G.orbitPower o (2*C+1)) ∨
        GraphTopology.HasFiniteApproximateQuotientCounterexample
          (G.orbitPower o (2*C+1)) (5^(d+2))) := by
  obtain ⟨d,hd,C,hconn,hinf,hloc,ht,hpoly,hpow,hfail⟩ :=
    G.main_failure_topological_classification_counterexample hc hl hq hpc hper o
  exact ⟨d,hd,C,hconn,hinf,hloc,ht,hpoly,hpow,
    GraphTopology.classification_failure_dichotomy _ hpow hfail⟩

end BondGraph
end CriticalPercolation
end
end

end OAI
