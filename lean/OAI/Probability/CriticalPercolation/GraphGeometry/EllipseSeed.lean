import Mathlib
import OAI.Probability.CriticalPercolation.Criticality.FavoredFinite
import OAI.Probability.CriticalPercolation.GraphGeometry.EllipseExit
import OAI.Probability.CriticalPercolation.GraphGeometry.GraphBalls

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def seedInfiniteEvent (A : Set V) : Set (Set E) :=
  {ω | ∃ a∈A, (G.cluster ω a).Infinite}

lemma seedInfiniteEvent_measurable [Countable V] [Countable E] (A : Set V) :
    MeasurableSet (G.seedInfiniteEvent A) := by
  have he : G.seedInfiniteEvent A=⋃ a∈A, {ω : Set E | (G.cluster ω a).Infinite} := by ext ω; simp [seedInfiniteEvent]
  rw [he]
  exact MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun _ => G.measurableSet_infiniteEvent a

lemma seedInfiniteEvent_mono {A B : Set V} (hAB : A⊆B) :
    G.seedInfiniteEvent A⊆G.seedInfiniteEvent B := by
  rintro ω ⟨a,ha,hi⟩
  exact ⟨a,hAB ha,hi⟩

theorem exists_seed_infinite_probability [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (o : V) (q : E → unitInterval)
    (hone : BernoulliProduct.law q G.percolates=1) (eps : ℝ) (heps : 0<eps) :
    ∃ m : ℕ, 1-eps<(BernoulliProduct.law q).real (G.seedInfiniteEvent (G.vertexBall o m)) := by
  let A : ℕ → Set (Set E) := fun n => G.seedInfiniteEvent (G.vertexBall o n)
  have hmono : Monotone A := fun _ _ h => G.seedInfiniteEvent_mono (G.vertexBall_mono o h)
  have heq : (⋃ n, A n)=G.percolates := by
    ext ω
    constructor
    · intro h
      obtain ⟨n,a,_ha,hi⟩ := Set.mem_iUnion.mp h
      exact ⟨a,hi⟩
    · rintro ⟨a,hi⟩
      obtain ⟨n,hn⟩ := G.reachable_mem_vertexBall (hc o a)
      exact Set.mem_iUnion.mpr ⟨n,a,hn,hi⟩
  have ht := tendsto_measure_iUnion_atTop (μ := BernoulliProduct.law q) hmono
  rw [heq,hone] at ht
  have hreal := (ENNReal.tendsto_toReal (by simp : (1 : ℝ≥0∞)≠⊤)).comp ht
  have hnear : ∀ᶠ n in atTop, 1-eps<(BernoulliProduct.law q).real (A n) :=
    hreal.eventually (lt_mem_nhds (by simpa using heps : 1-eps<ENNReal.toReal 1))
  exact hnear.exists

theorem exists_favored_ellipse [Countable E]
    (Psi : V → ℂ) (A : Set V) (zeta D : ℝ) (hD : 0≤D) (hDz : D≤zeta)
    (hPsi : ∀ ⦃x y⦄, G.fullGraph.Adj x y → ‖Psi x-Psi y‖≤D)
    (hseed : ∀ a∈A, ‖Psi a‖<1) (S : Finset Circle)
    (hcover : ∀ c : Circle, ∃ d∈S, ‖(c : ℂ)-(d : ℂ)‖<zeta)
    (q : E → unitInterval) (a : ℝ) (ha : 0≤a)
    (hi : 1-a^S.card<(BernoulliProduct.law q).real (G.seedInfiniteEvent A))
    (hbound : ∀ᵐ ω ∂BernoulliProduct.law q, ∀ x∈A,
      (G.cluster (ω∩G.inducedEdges {x | ‖Psi x‖≤1}) x).Finite) :
    ∃ c∈S, 1-a<(BernoulliProduct.law q).real (G.ellipseExit Psi A zeta c) := by
  have hsub : G.seedInfiniteEvent A ≤ᵐ[BernoulliProduct.law q] ⋃ c∈S, G.ellipseExit Psi A zeta c := by
    filter_upwards [hbound] with ω hω
    exact fun hi => G.infinite_cluster_ellipseExit Psi A zeta D hD hDz hPsi hseed S hcover hi hω
  have hprob := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
  exact BernoulliProduct.exists_favored_finite q (fun c => G.ellipseExit Psi A zeta c) S
    (fun c _ => G.ellipseExit_upper Psi A zeta c) (fun c _ => G.ellipseExit_finiteWitness Psi A zeta c)
    a ha (hi.trans_le hprob)

end CriticalPercolation.BondGraph
end
end
end

end OAI
