import OAI.Analysis.AncientFlat.Evolution.DilationCore

namespace OAI
noncomputable section
open Set Filter
open scoped Topology ZeroAtInfty BoundedContinuousFunction
namespace ParametrixDilation
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
lemma dist_dil_le (t : ℝ) (f g : C₀(V,ℂ)) : dist (dil t f) (dil t g)≤dist f g := by
  let : NormedAddCommGroup C₀(V,ℂ) := inferInstance
  let : NormedSpace ℂ C₀(V,ℂ) := inferInstance
  rw [dist_eq_norm,dist_eq_norm,←map_sub]
  exact norm_dil_le t (f-g)
lemma tendsto_dil_apply {ι : Type*} {l : Filter ι} {r : ι → ℝ} {u : ι → C₀(V,ℂ)}
    {r₀ : ℝ} {u₀ : C₀(V,ℂ)} (hr : Tendsto r l (𝓝 r₀)) (hu : Tendsto u l (𝓝 u₀)) :
    Tendsto (fun i => dil (r i) (u i)) l (𝓝 (dil r₀ u₀)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  have h₁ := tendsto_iff_dist_tendsto_zero.mp hu
  have h₂ := tendsto_iff_dist_tendsto_zero.mp (((continuous_dil u₀).tendsto r₀).comp hr)
  apply squeeze_zero (fun i => dist_nonneg) (fun i => ?_) (by simpa using h₁.add h₂)
  exact (dist_triangle _ (dil (r i) u₀) _).trans
    (add_le_add (dist_dil_le (r i) (u i) u₀) le_rfl)
lemma continuousOn_dil_apply {u : ℝ → C₀(V,ℂ)} {I : Set ℝ}
    (hu : ContinuousOn u I) : ContinuousOn (fun t => dil t (u t)) I := by
  intro t ht
  exact tendsto_dil_apply continuousWithinAt_id (hu t ht)
end ParametrixDilation

end

end OAI
