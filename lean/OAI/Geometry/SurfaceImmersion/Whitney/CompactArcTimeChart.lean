import OAI.Geometry.SurfaceImmersion.Atlas.JoinTimeCharts
import OAI.Geometry.SurfaceImmersion.Whitney.ArcTimeGermPartition

namespace OAI

/-! One actual smooth source chart around the entire compact embedded arc. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [SigmaCompactSpace M] [Nonempty M]

theorem compact_arc_time_chart (P : SmoothCompactArc planeModel M)
    {F : M → ℝ} (hF : ContMDiff planeModel 𝓘(ℝ) ∞ F)
    (hFP : ∀ t ∈ Icc P.start P.finish, F (P.curve t) = t) :
    ∃ c : SurfaceTimeChart F, ∀ t ∈ Icc P.start P.finish,
      ∀ᶠ s in 𝓝[Icc P.start P.finish] t,
        P.curve s ∈ c.coord.source ∧ c.coord (P.curve s) = ![0,s] := by
  obtain ⟨τ,N,hzero,hmono,hbounds,hend,hcharts⟩ := arc_time_chart_germ_partition P hF hFP
  have hγ : ∀ t ∈ Icc P.start P.finish, ContinuousAt P.curve t := by
    intro t ht
    exact (P.smooth.contMDiffAt (P.domain_open.mem_nhds (P.interval_subset ht))).continuousAt
  have hstep : ∀ n : ℕ, ∃ c : SurfaceTimeChart F,
      ∀ t ∈ Icc P.start (τ n), ∀ᶠ s in 𝓝[Icc P.start P.finish] t,
        P.curve s ∈ c.coord.source ∧ c.coord (P.curve s) = ![0,s] := by
    intro n
    induction n with
    | zero =>
      obtain ⟨c,hc⟩ := hcharts 0
      refine ⟨c,?_⟩
      intro t ht
      have ht0 : t = P.start := le_antisymm (ht.2.trans_eq hzero) ht.1
      apply hc t
      constructor
      · rw [ht0,hzero]
      · rw [ht0]
        exact (hbounds 1).1
    | succ n ih =>
      obtain ⟨c,hc⟩ := ih
      obtain ⟨d,hd⟩ := hcharts n
      by_cases hn : τ n = P.start
      · refine ⟨d,?_⟩
        intro t ht
        exact hd t ⟨hn.symm ▸ ht.1,ht.2⟩
      · by_cases heq : τ (n+1) = τ n
        · refine ⟨c,?_⟩
          intro t ht
          exact hc t ⟨ht.1,heq ▸ ht.2⟩
        · have hsn : P.start < τ n := lt_of_le_of_ne (hbounds n).1 (Ne.symm hn)
          have hns : τ n < τ (n+1) := lt_of_le_of_ne (hmono (Nat.le_succ n)) (Ne.symm heq)
          apply join_time_charts hF hsn hns
            (fun t ht => hγ t ⟨ht.1,ht.2.trans (hbounds (n+1)).2⟩)
            (Icc_mem_nhds hsn (hns.trans_le (hbounds (n+1)).2))
            (fun t ht => ⟨ht.1,ht.2.trans (hbounds (n+1)).2⟩) c d hc hd
  obtain ⟨c,hc⟩ := hstep N
  refine ⟨c,?_⟩
  intro t ht
  apply hc t
  rwa [hend N le_rfl]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
