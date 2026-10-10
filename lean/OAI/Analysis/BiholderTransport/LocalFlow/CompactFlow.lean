import Mathlib
import OAI.Analysis.BiholderTransport.LocalFlow.MIntegralCurveUniformInvariant

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
open scoped NNReal

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology
open MeasureTheory
open scoped ContDiff ENNReal

open Set Filter Manifold Bundle ContinuousLinearMap MeasureTheory
open scoped Topology ContDiff Manifold Bundle ENNReal

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology Manifold

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Bundle
open scoped Topology Bundle

open scoped Topology
open Function Manifold Set
open Manifold Bundle
open scoped Manifold Bundle

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [HasContDiffBump E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

lemma exists_uniform_time_on_compact {v : (x : M) → TangentSpace I x}
    (hv : ContMDiff I (I.prod 𝓘(ℝ,E)) ∞ (fun x => (⟨x,v x⟩ : TangentBundle I M)))
    {K : Set M} (hK : IsCompact K) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ K,
      ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurveOn γ v (Ioo (-ε) ε) := by
  classical
  choose r hr U hU hflow using exists_uniform_local_manifold_curves hv
  obtain ⟨t,_,ht⟩ := hK.elim_nhds_subcover U (fun x _ => hU x)
  have hfin : ∀ t : Finset M, ∃ ε : ℝ, 0 < ε ∧ ∀ a ∈ t, ε ≤ r a := by
    intro s
    induction s using Finset.induction with
    | empty => exact ⟨1,by norm_num,by simp⟩
    | @insert a s ha ih =>
      obtain ⟨ε,hε,hle⟩ := ih
      refine ⟨min ε (r a),lt_min hε (hr a),?_⟩
      intro b hb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hle b hb)
  obtain ⟨ε,hε,hle⟩ := hfin t
  refine ⟨ε,hε,?_⟩
  intro x hx
  obtain ⟨a,ha,hxa⟩ := mem_iUnion₂.mp (ht hx)
  obtain ⟨γ,hγ0,hγ⟩ := hflow a x hxa
  exact ⟨γ,hγ0,hγ.mono (Ioo_subset_Ioo (neg_le_neg (hle a ha)) (hle a ha))⟩

lemma exists_complete_curve_of_compact_invariant [T2Space M]
    {v : (x : M) → TangentSpace I x}
    (hv : ContMDiff I (I.prod 𝓘(ℝ,E)) ∞ (fun x => (⟨x,v x⟩ : TangentBundle I M)))
    {K : Set M} (hK : IsCompact K)
    (hinv : ∀ (a : ℝ) (γ : ℝ → M), γ 0 ∈ K →
      IsMIntegralCurveOn γ v (Ioo (-a) a) → MapsTo γ (Ioo (-a) a) K)
    (x : M) (hx : x ∈ K) : ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v := by
  obtain ⟨ε,hε,hflow⟩ := exists_uniform_time_on_compact hv hK
  exact exists_isMIntegralCurve_of_uniform_invariant_set (hv.of_le (by simp))
    hε hflow hinv x hx

end WeakMTWTransport

end

end OAI
