import OAI.Probability.BenjaminiSchramm.GhostPivotalUnion
import OAI.Probability.BenjaminiSchramm.GhostPivotalIncidence
import OAI.Probability.BenjaminiSchramm.FiniteClusterSums
import OAI.Probability.BenjaminiSchramm.GhostDoubleConnection
import OAI.Probability.BenjaminiSchramm.GhostDerivative

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal NNReal BigOperators

namespace Percolation.BenjaminiSchramm

theorem lintegral_twice_tsum {A I : Type*} [MeasurableSpace A] [Countable I]
    (ν : Measure A) [SFinite ν] (F : I → A × A → ℝ≥0∞)
    (hF : ∀ i, Measurable (F i)) :
    (∫⁻ m, ∫⁻ n, ∑' i, F i (m,n) ∂ν ∂ν) =
      ∑' i, ∫⁻ m, ∫⁻ n, F i (m,n) ∂ν ∂ν := by
  calc
    _ = ∫⁻ z, ∑' i, F i z ∂ν.prod ν :=
      (lintegral_prod _ (Measurable.tsum hF).aemeasurable).symm
    _ = ∑' i, ∫⁻ z, F i z ∂ν.prod ν := lintegral_tsum (fun i => (hF i).aemeasurable)
    _ = _ := tsum_congr fun i => lintegral_prod _ (hF i).aemeasurable

variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

lemma measurable_ghostBridge_cluster_fields (p : unitInterval) (x : V)
    (e : E) (u v : V) (S : Finset V) :
    Measurable (fun z : Set V × Set V => law p {ω |
      GhostBridgePivotal G ω z.1 z.2 x e u v ∧ cluster G (ω \ {e}) x = (S : Set V)}) := by
  have hdel : Measurable (fun ω : Set E => ω \ {e}) :=
    measurable_set_iff.mpr fun f => (measurable_set_mem f).and measurable_const
  have hm := (measurableSet_ghostBridgePivotal G x e u v).inter
    ((((criticalModel G).measurableSet_exactCluster x (S : Set V)).preimage hdel).preimage measurable_snd)
  convert measurable_measure_prodMk_left (ν := law p) hm using 1
  funext z
  congr 1
  ext ω
  simp only [Set.mem_inter_iff,Set.mem_preimage,Set.mem_ofPred_eq,criticalModel_cluster]

theorem averaged_twoGhost_le_fan_add_pivotal_sum (hG : Function.Injective G)
    (p : unitInterval) (x : V) (hfin : ∀ᵐ ω ∂law p, (cluster G ω x).Finite)
    (ν : Measure (Set V)) [SFinite ν] :
    (∫⁻ m, ∫⁻ n, law p (finiteGhostConnection G x id m ∩ finiteGhostConnection G x id n) ∂ν ∂ν) ≤
      (∫⁻ m, law p (finiteGhostConnection G x id m) ∂ν)^2 +
      ∑' e : E, ∑' u : V, ∑' v : V, ∑' S : Finset V,
        ∫⁻ m, ∫⁻ n, law p {ω | GhostBridgePivotal G ω m n x e u v ∧
          cluster G (ω \ {e}) x = (S : Set V)} ∂ν ∂ν := by
  let F := fun e u v (S : Finset V) (z : Set V × Set V) => law p {ω |
    GhostBridgePivotal G ω z.1 z.2 x e u v ∧ cluster G (ω \ {e}) x = (S : Set V)}
  let D := fun z : Set V × Set V => law p
    (DisjointOccurrence (finiteGhostConnection G x id z.1) (finiteGhostConnection G x id z.2))
  have hF (e : E) (u v : V) (S : Finset V) : Measurable (F e u v S) :=
    measurable_ghostBridge_cluster_fields G p x e u v S
  have hD : Measurable D := measurable_measure_prodMk_left (ν := law p)
    (measurableSet_ghostDisjointOccurrence G x id)
  have hsum : (∫⁻ m, ∫⁻ n, ∑' e, ∑' u, ∑' v, ∑' S, F e u v S (m,n) ∂ν ∂ν) =
      ∑' e, ∑' u, ∑' v, ∑' S, ∫⁻ m, ∫⁻ n, F e u v S (m,n) ∂ν ∂ν := by
    rw [lintegral_twice_tsum ν _ (fun e => Measurable.tsum fun u => Measurable.tsum fun v => Measurable.tsum (hF e u v))]
    apply tsum_congr
    intro e
    rw [lintegral_twice_tsum ν _ (fun u => Measurable.tsum fun v => Measurable.tsum (hF e u v))]
    apply tsum_congr
    intro u
    rw [lintegral_twice_tsum ν _ (fun v => Measurable.tsum (hF e u v))]
    apply tsum_congr
    intro v
    exact lintegral_twice_tsum ν _ (hF e u v)
  calc
    _ ≤ ∫⁻ m, ∫⁻ n, D (m,n) + ∑' e, ∑' u, ∑' v, ∑' S, F e u v S (m,n) ∂ν ∂ν := by
      apply lintegral_mono
      intro m
      apply lintegral_mono
      intro n
      exact twoGhostConnection_le_fan_add_pivotal_sum G hG p x m n hfin
    _ = (∫⁻ m, ∫⁻ n, D (m,n) ∂ν ∂ν) +
        ∫⁻ m, ∫⁻ n, ∑' e, ∑' u, ∑' v, ∑' S, F e u v S (m,n) ∂ν ∂ν := by
      have hM : Measurable (fun z => ∑' e, ∑' u, ∑' v, ∑' S, F e u v S z) :=
        Measurable.tsum fun e => Measurable.tsum fun u => Measurable.tsum fun v => Measurable.tsum (hF e u v)
      have hDM : Measurable (fun z => D z + ∑' e, ∑' u, ∑' v, ∑' S, F e u v S z) := hD.add hM
      rw [←lintegral_prod _ hDM.aemeasurable,lintegral_add_left hD _,
        lintegral_prod _ hD.aemeasurable,lintegral_prod _ hM.aemeasurable]
    _ ≤ _ := by
      rw [hsum]
      exact add_le_add (averaged_ghostConnection_bk G x id p ν) le_rfl

end Percolation.BenjaminiSchramm

end

end OAI
