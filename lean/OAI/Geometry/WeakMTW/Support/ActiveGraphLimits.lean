import Mathlib
import OAI.Geometry.WeakMTW.Variations.CostSplitting
import OAI.Geometry.WeakMTW.Support.FiniteActiveGraph

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]
  {ι : Type*} [Fintype ι] [Nonempty ι]

omit [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M] in
 theorem tangentBundle_firstCountable : FirstCountableTopology (TangentBundle (model n) M) := by
  constructor
  intro p
  have hp : p ∈ (RiemannianLocal.stateChart p.1).source :=
    (RiemannianLocal.stateChart_source p.1 p).mpr (mem_chart_source (Model n) p.1)
  rw [(RiemannianLocal.stateChart p.1).nhds_eq_comap_inf_principal hp]
  infer_instance

 theorem active_velocity_subseq (y : ι → M) (h : ι → ℝ)
    {p : ℕ → M} {x : M} (hp : Tendsto p atTop (𝓝 x))
    (a : ∀ j, TangentSpace (model n) (p j))
    (ha : ∀ j, a j ∈ activeVelocities y h (p j)) :
    ∃ a₀ ∈ activeVelocities y h x, ∃ ρ : ℕ → ℕ, StrictMono ρ ∧
      Tendsto (fun j => (⟨p (ρ j),a (ρ j)⟩ : TangentBundle (model n) M)) atTop (𝓝 ⟨x,a₀⟩) := by
  let := tangentBundle_firstCountable (n := n) (M := M)
  obtain ⟨⟨z,a₀⟩,ha₀,ρ,hρ,hlim⟩ := (activeGraph_compact y h).tendsto_subseq
    (fun j => show (⟨p j,a j⟩ : TangentBundle (model n) M) ∈ activeGraph y h from ha j)
  have hb : Continuous (fun q : TangentBundle (model n) M => q.1) :=
    (contMDiff_proj (TangentSpace (model n)) (IB := model n) (n := ∞)).continuous
  have hz : z = x := tendsto_nhds_unique (hb.continuousAt.tendsto.comp hlim) (hp.comp hρ.tendsto_atTop)
  subst z
  exact ⟨a₀,ha₀,ρ,hρ,hlim⟩

 theorem shortened_upper_difference {x : M} {w : TangentSpace (model n) x}
    (hw : w ∈ minimizingDomain x) {ℓ : ℝ} (hℓ : 0 < ℓ) (hℓ₁ : ℓ < 1) (z : M) :
    cost z (exp x w)-cost x (exp x w) ≤
      (cost z (exp x (ℓ•w))-cost x (exp x (ℓ•w)))/ℓ := by
  have hsplit := cost_triangle_split z (exp x (ℓ•w)) (exp x w) hℓ (sub_pos.mpr hℓ₁)
  have hdist := minimizing_shortened_dist hw hℓ.le hℓ₁.le (le_refl 1)
  simp only [one_smul] at hdist
  have htail : cost (exp x (ℓ•w)) (exp x w) = (1-ℓ)^2*‖w‖^2/2 := by
    unfold cost
    rw [hdist,mul_pow]
  have hbase : cost x (exp x w) = ‖w‖^2/2 := by
    unfold cost
    rw [show dist x (exp x w) = ‖w‖ from hw]
  rw [add_sub_cancel,div_one,htail] at hsplit
  rw [hbase,minimizing_shortened_cost hw hℓ.le hℓ₁.le]
  have hid : (1-ℓ)^2*‖w‖^2/2/(1-ℓ)-‖w‖^2/2 = -(ℓ^2*‖w‖^2/2)/ℓ := by
    field_simp [hℓ.ne',(sub_pos.mpr hℓ₁).ne']
    ring
  rw [neg_div] at hid
  rw [sub_div]
  linarith

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
