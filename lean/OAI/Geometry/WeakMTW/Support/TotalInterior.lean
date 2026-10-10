import Mathlib
import OAI.Geometry.WeakMTW.Coordinates.InteriorCost

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 def totalInterior : Set (TangentBundle (model n) M) := {p | p.2 ∈ injectivityDomain p.1}

 theorem totalInterior_mem_interior {x : M} {v : TangentSpace (model n) x}
    (hv : v ∈ injectivityDomain x) :
    (⟨x,v⟩ : TangentBundle (model n) M) ∈ interior totalMinimizingSet := by
  let y := exp x v
  obtain ⟨e,he,hev,hes,hei⟩ := pairExpCoordinates_local_inverse x y hv (mem_chart_source (Model n) y)
  let U : Set (TangentBundle (model n) M) := (stateChart x).source ∩ stateChart x ⁻¹' e.source
  have hU : IsOpen U := (stateChart x).continuousOn.isOpen_inter_preimage (stateChart x).open_source e.open_source
  have hsrc : (⟨x,v⟩ : TangentBundle (model n) M) ∈ (stateChart x).source :=
    (stateChart_source x _).mpr (mem_chart_source (Model n) x)
  have hvU : (⟨x,v⟩ : TangentBundle (model n) M) ∈ U := ⟨hsrc,hev⟩
  have hnear := minimizing_states_near_unique x hv hU hvU
  have hinj : InjOn baseExp U := by
    intro p hp q hq heq
    apply (stateChart x).injOn hp.1 hq.1
    apply e.injOn hp.2 hq.2
    rw [he,pairExpCoordinates_state x y p hp.1,pairExpCoordinates_state x y q hq.1]
    exact Prod.ext (congrArg (fun z : M × M => chartAt (Model n) x z.1) heq)
      (congrArg (fun z : M × M => chartAt (Model n) y z.2) heq)
  apply mem_interior_iff_mem_nhds.mpr
  have hbase := baseExp_continuous.continuousAt.tendsto (x := (⟨x,v⟩ : TangentBundle (model n) M))
  filter_upwards [hU.mem_nhds hvU,hbase hnear] with p hp hpn
  obtain ⟨w,hew,hnw⟩ := exists_minimizing_vector (n := n) p.1 (exp p.1 p.2)
  let q : TangentBundle (model n) M := ⟨p.1,w⟩
  have hqM : q ∈ totalMinimizingSet := by change dist p.1 (exp p.1 w) = ‖w‖; rw [hew,hnw]
  have hqE : baseExp q = baseExp p := Prod.ext rfl hew
  have hqU : q ∈ U := hpn q hqM hqE
  have hqp : q = p := hinj hqU hp hqE
  exact hqp ▸ hqM

 omit [IsContMDiffRiemannianBundle (model n) ∞ (Model n)
   (fun x : M => TangentSpace (model n) x)] [IsRiemannianManifold (model n) M]
   [CompactSpace M] in
 theorem interior_totalMinimizingSet_subset :
    interior (totalMinimizingSet (n := n) (M := M)) ⊆ totalInterior := by
  rintro ⟨x,v⟩ hp
  have hcont : Continuous (fun t : ℝ => (⟨x,t•v⟩ : TangentBundle (model n) M)) :=
    (FiberBundle.continuous_totalSpaceMk (Model n) (TangentSpace (model n)) x).comp
      (continuous_id.smul continuous_const)
  have hnear : ∀ᶠ t : ℝ in 𝓝 (1 : ℝ), (⟨x,t•v⟩ : TangentBundle (model n) M) ∈ totalMinimizingSet := by
    have hn : totalMinimizingSet ∈ 𝓝 (⟨x,(1 : ℝ)•v⟩ : TangentBundle (model n) M) := by
      simpa only [one_smul] using (mem_interior_iff_mem_nhds.mp hp)
    exact hcont.continuousAt.preimage_mem_nhds hn
  obtain ⟨a,ha,haM⟩ : ∃ a : ℝ, 1 < a ∧ (⟨x,a•v⟩ : TangentBundle (model n) M) ∈ totalMinimizingSet := by
    obtain ⟨a,haM,ha⟩ := (hnear.filter_mono nhdsWithin_le_nhds |>.and
      (self_mem_nhdsWithin : ∀ᶠ a : ℝ in 𝓝[>] (1 : ℝ), a ∈ Ioi 1)).exists
    exact ⟨a,ha,haM⟩
  refine ⟨a,ha,?_⟩
  change dist x (exp x (a•v)) = ‖a•v‖ at haM
  simpa only [norm_smul,Real.norm_eq_abs,abs_of_pos (lt_trans zero_lt_one ha)] using haM

 theorem totalInterior_eq_interior : totalInterior (n := n) (M := M) = interior totalMinimizingSet := by
  apply Subset.antisymm
  · rintro ⟨x,v⟩ hv
    exact totalInterior_mem_interior hv
  · exact interior_totalMinimizingSet_subset

 theorem totalInterior_open : IsOpen (totalInterior (n := n) (M := M)) := by
  rw [totalInterior_eq_interior]
  exact isOpen_interior

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
