import Mathlib
import OAI.Geometry.WeakMTW.Coordinates.RadialCoordinates

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter
open scoped Topology ContDiff

namespace NormalNeighborhood.NormalFlow
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
open CoordinateGeometry GeodesicScaling
variable {G : E → MetricTensor E} {S : Set E} {x₀ : E}

theorem normal_rescaled_curve (N : NormalFlow G S x₀)
    (hS : IsOpen S) (hG : ContDiffOn ℝ ∞ G S)
    (hpos : ∀ z ∈ S, ∀ v : E, v ≠ 0 → 0 < G z v v)
    {q : ℝ → E × E} {a b : ℝ}
    (hq : ∀ t ∈ Icc (0 : ℝ) N.time, (q (a + b * t)).1 ∈ S ∧
      HasDerivAt q (geodesicSpray G (q (a + b * t))) (a + b * t))
    (hv : b • (q a).2 ∈ (N.normalAt (q a).1).source) :
    N.normalAt (q a).1 (b • (q a).2) = (q (a + b * N.time)).1 := by
  let u : ℝ → E × E := fun t => N.flow (t, scalePhase b (q a))
  let v : ℝ → E × E := fun t => scalePhase b (q (a + b * t))
  have hseg := N.source_stays ((q a).1, b • (q a).2) hv
  have hdu : ∀ t ∈ Icc (0 : ℝ) N.time, HasDerivAt u (geodesicSpray G (u t)) t :=
    fun t ht => (N.ode _ (hseg t ht)).2
  have hdv : ∀ t ∈ Icc (0 : ℝ) N.time, HasDerivAt v (geodesicSpray G (v t)) t := by
    intro t ht
    have hd := (hq t ht).2.scomp t (((hasDerivAt_id t).const_mul b).const_add a)
    have he := (scalePhase b).hasFDerivAt.comp_hasDerivAt t hd
    simpa only [mul_one, scale_spray, Function.comp_def, id_eq, v] using he
  have hf : ∀ z ∈ u '' Icc (0 : ℝ) N.time ∪ v '' Icc (0 : ℝ) N.time,
      ContDiffAt ℝ 1 (geodesicSpray G) z := by
    intro z hz
    have hzS : z.1 ∈ S := by
      rcases hz with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
      · exact (N.ode _ (hseg t ht)).1
      · exact (hq t ht).1
    exact (((contDiffOn_geodesicSpray hS hG hpos) z ⟨hzS, mem_univ _⟩).contDiffAt
      ((hS.prod isOpen_univ).mem_nhds ⟨hzS, mem_univ _⟩)).of_le (by simp)
  have hzero : u 0 = v 0 := by
    dsimp [u, v]
    rw [N.initial _ (hseg 0 ⟨le_rfl, N.time_pos.le⟩)]
    simp
  have he := FlowLinearization.unique_Icc
    (fun t ht => (hdu t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hdv t ht).continuousAt.continuousWithinAt) hf
    (fun t ht => (hdu t ht).hasDerivWithinAt)
    (fun t ht => (hdv t ht).hasDerivWithinAt) hzero ⟨N.time_pos.le, le_rfl⟩
  rw [normalAt_apply]
  have he' := congrArg (fun p : E × E => p.1) he
  exact he'

end
end NormalNeighborhood.NormalFlow
end

end WeakMTWGlobalSupport

end OAI
