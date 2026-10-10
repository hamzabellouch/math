import Mathlib
import OAI.Analysis.BiholderTransport.CostGeometry.UniformLocalGap
import OAI.Analysis.BiholderTransport.CostGeometry.LimitIsolation
import OAI.Analysis.BiholderTransport.CostGeometry.PrecutExtension

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.extend_injective_graphProjection
    (hmtw : WeakMTW (n := n) (M := M)) {v : M → ℝ} (hv : Continuous v)
    {T : ℝ} (hT : 0<T) (hT1 : T<1)
    (hinj : ∀ t ∈ Ioo (0:ℝ) T, Function.Injective (graphProjection (n := n) (cTransform v) t)) :
    ∃ R, T<R ∧ R<1 ∧ ∀ t ∈ Ioc (0:ℝ) R,
      Function.Injective (graphProjection (n := n) (cTransform v) t) := by
  let : CompactSpace (subgradientGraph (n := n) (cTransform v)) :=
    isCompact_iff_compactSpace.mp (isCompact_subgradientGraph hv)
  have hTI := hmtw.injective_graphProjection_at_left_limit hv hT hT1 hinj
  have hID := hmtw.active_hull_precut_at_left_limit hv hT hT1 hinj
  obtain ⟨S,hTS,hS1,hSID⟩ := exists_extended_uniform_precut hv hT hT1 hID
  obtain ⟨δ,hδ,hsep⟩ := hmtw.uniform_graph_fiber_separation hv hS1 hSID
  have hnear : ∀ᶠ t in 𝓝 T, Function.Injective (graphProjection (n := n) (cTransform v) t) := by
    apply eventually_injective_of_uniform_local_injective
      (graphProjection (n := n) (cTransform v)) (continuous_graphProjection_family _)
      (fun z => z.1.1) ((FiberBundle.continuous_proj _ _).comp continuous_subtype_val) hδ hTI
    filter_upwards [eventually_gt_nhds hT,eventually_lt_nhds hTS] with t ht htS
    exact hsep t ⟨ht,htS.le⟩
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hnear
  let R := T+min (ε/2) ((1-T)/2)
  have hTR : T<R := by dsimp [R]; have : 0 < min (ε/2) ((1-T)/2) := lt_min (by linarith) (by linarith); linarith
  have hR1 : R<1 := by have := min_le_right (ε/2) ((1-T)/2); dsimp [R]; linarith
  have hRε : R<T+ε := by have := min_le_left (ε/2) ((1-T)/2); dsimp [R]; linarith
  refine ⟨R,hTR,hR1,?_⟩
  intro t ht
  by_cases htT : t<T
  · exact hinj t ⟨ht.1,htT⟩
  · apply hball
    rw [Metric.mem_ball,Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr (le_of_not_gt htT))]
    linarith [ht.2]

lemma WeakMTW.injective_graphProjection
    (hmtw : WeakMTW (n := n) (M := M)) {v : M → ℝ} (hv : Continuous v)
    {t : ℝ} (ht : 0<t) (ht1 : t<1) :
    Function.Injective (graphProjection (n := n) (cTransform v) t) := by
  let A : Set ℝ := {T | 0<T ∧ T<1 ∧ ∀ s ∈ Ioc (0:ℝ) T,
    Function.Injective (graphProjection (n := n) (cTransform v) s)}
  obtain ⟨τ,hτ,hτ1,hτI⟩ := hmtw.exists_short_injective_graphProjection hv
  have hτA : τ∈A := ⟨hτ,hτ1,hτI⟩
  have hA : A.Nonempty := ⟨τ,hτA⟩
  have hAb : BddAbove A := ⟨1,fun _ h => h.2.1.le⟩
  have hB : 0<sSup A := hτ.trans_le (le_csSup hAb hτA)
  have hB1 : sSup A≤1 := csSup_le hA (fun _ h => h.2.1.le)
  have hBI : ∀ s ∈ Ioo (0:ℝ) (sSup A),
      Function.Injective (graphProjection (n := n) (cTransform v) s) := by
    intro s hs
    obtain ⟨R,hRA,hsR⟩ := exists_lt_of_lt_csSup hA hs.2
    exact hRA.2.2 s ⟨hs.1,hsR.le⟩
  have heq : sSup A=1 := by
    apply le_antisymm hB1
    by_contra hn
    obtain ⟨R,hBR,hR1,hRI⟩ := hmtw.extend_injective_graphProjection hv hB (lt_of_not_ge hn) hBI
    have hRA : R∈A := ⟨hB.trans hBR,hR1,hRI⟩
    exact (not_lt_of_ge (le_csSup hAb hRA)) hBR
  apply hBI t
  exact ⟨ht,by rwa [heq]⟩

lemma WeakMTW.active_hull_precut
    (hmtw : WeakMTW (n := n) (M := M)) {v : M → ℝ} (hv : Continuous v)
    {t : ℝ} (ht : 0<t) (ht1 : t<1) :
    ∀ x : M, ∀ p ∈ convexHull ℝ (activeLogs (n := n) v x), t • p ∈ injectivityDomain x :=
  hmtw.active_hull_precut_at_left_limit hv ht ht1
    (fun _ hs => hmtw.injective_graphProjection hv hs.1 (hs.2.trans ht1))

end WeakMTWTransport

end

end OAI
