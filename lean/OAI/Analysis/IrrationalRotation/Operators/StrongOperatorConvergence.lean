import OAI.Analysis.IrrationalRotation.Analysis.StrongFieldContinuity
import Mathlib.Analysis.InnerProductSpace.l2Space

namespace OAI

open Filter
open scoped Topology
namespace Invariant233

variable {𝕜 E F ι : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem strong_tendsto_of_dense_of_bounded
    {l : Filter ι} {A : ι → E →L[𝕜] F} {A₀ : E →L[𝕜] F}
    {s : Set E} {C : ℝ} (hs : Dense s)
    (hA : ∀ w ∈ s, Tendsto (fun i => A i w) l (𝓝 (A₀ w)))
    (hC : ∀ᶠ i in l, ‖A i‖ ≤ C) (v : E) :
    Tendsto (fun i => A i v) l (𝓝 (A₀ v)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let M : ℝ := max C 0 + ‖A₀‖ + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hCM : C ≤ M := by dsimp [M]; have := le_max_left C 0; have := norm_nonneg A₀; linarith
  have hAM : ‖A₀‖ ≤ M := by dsimp [M]; have := le_max_right C 0; linarith
  obtain ⟨w, hws, hvw⟩ := hs.exists_dist_lt v (div_pos (show 0 < ε / 3 by positivity) hM)
  have hMw : M * dist v w < ε / 3 := by
    simpa [mul_comm] using (lt_div_iff₀ hM).mp hvw
  have hw := Metric.tendsto_nhds.mp (hA w hws) (ε / 3) (by positivity)
  filter_upwards [hC, hw] with i hi hwi
  have hfirst : dist (A i v) (A i w) < ε / 3 :=
    ((A i).dist_le_opNorm v w).trans_lt
      ((mul_le_mul_of_nonneg_right (hi.trans hCM) dist_nonneg).trans_lt hMw)
  have hlast : dist (A₀ w) (A₀ v) < ε / 3 := by
    rw [dist_comm]
    exact (A₀.dist_le_opNorm v w).trans_lt
      ((mul_le_mul_of_nonneg_right hAM dist_nonneg).trans_lt hMw)
  have htri := dist_triangle (A i v) (A i w) (A₀ v)
  have htri' := dist_triangle (A i w) (A₀ w) (A₀ v)
  linarith

theorem strong_tendsto_of_dense_span_of_bounded
    {κ : Type*} {l : Filter ι} {A : ι → E →L[𝕜] F} {A₀ : E →L[𝕜] F}
    {b : κ → E} {C : ℝ}
    (hb : Dense (Submodule.span 𝕜 (Set.range b) : Set E))
    (hA : ∀ k, Tendsto (fun i => A i (b k)) l (𝓝 (A₀ (b k))))
    (hC : ∀ᶠ i in l, ‖A i‖ ≤ C) (v : E) :
    Tendsto (fun i => A i v) l (𝓝 (A₀ v)) := by
  apply strong_tendsto_of_dense_of_bounded hb ?_ hC v
  intro w hw
  induction hw using Submodule.span_induction with
  | mem w hw => obtain ⟨k, rfl⟩ := hw; exact hA k
  | zero => simpa only [map_zero] using (tendsto_const_nhds : Tendsto (fun _ : ι => (0 : F)) l (𝓝 0))
  | add w z hw hz ihw ihz => simpa only [map_add] using ihw.add ihz
  | smul c w hw ih => simpa only [map_smul] using ih.const_smul c

end Invariant233

end OAI
