import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Tactic.Positivity

namespace OAI

namespace InvariantProjection

open Filter Topology

variable {𝕜 E F G ι X : Type*}
variable [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable [NormedAddCommGroup G] [NormedSpace 𝕜 G]

theorem tendsto_apply_of_strong_tendsto_of_bounded
    {l : Filter ι} {A : ι → E →L[𝕜] F} {A₀ : E →L[𝕜] F}
    {v : ι → E} {v₀ : E} {C : ℝ}
    (hA : ∀ w, Tendsto (fun i => A i w) l (𝓝 (A₀ w)))
    (hC : ∀ᶠ i in l, ‖A i‖ ≤ C)
    (hv : Tendsto v l (𝓝 v₀)) :
    Tendsto (fun i => A i (v i)) l (𝓝 (A₀ v₀)) := by
  have hnorm : Tendsto (fun i => C * ‖v i - v₀‖) l (𝓝 0) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ι => C) l (𝓝 C)).mul
      (hv.sub_const v₀).norm
  have hzero : Tendsto (fun i => A i (v i - v₀)) l (𝓝 0) := by
    apply squeeze_zero_norm' _ hnorm
    filter_upwards [hC] with i hi
    exact ((A i).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right hi (norm_nonneg _))
  have hsum := hzero.add (hA v₀)
  simpa only [map_sub, sub_add_cancel, zero_add] using hsum

variable [TopologicalSpace X]

theorem strong_continuous_of_dense_of_bounded
    {A : X → E →L[𝕜] F} {s : Set E} {C : ℝ}
    (hs : Dense s) (hA : ∀ w ∈ s, Continuous (fun x => A x w))
    (hC : ∀ x, ‖A x‖ ≤ C) (v : E) :
    Continuous (fun x => A x v) := by
  apply continuous_of_uniform_approx_of_continuous
  intro u hu
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_uniformity_dist.mp hu
  let M : ℝ := max C 0 + 1
  have hM : 0 < M := by dsimp [M]; positivity
  obtain ⟨w, hw, hvw⟩ := hs.exists_dist_lt v (div_pos hε hM)
  refine ⟨(fun x => A x w), hA w hw, ?_⟩
  intro x
  apply hsub
  calc
    dist (A x v) (A x w) ≤ ‖A x‖ * dist v w := (A x).dist_le_opNorm v w
    _ ≤ M * dist v w := mul_le_mul_of_nonneg_right
      ((hC x).trans ((le_max_left C 0).trans (by dsimp [M]; exact le_add_of_nonneg_right zero_le_one)))
      (dist_nonneg)
    _ < ε := by simpa [mul_comm] using (lt_div_iff₀ hM).mp hvw

theorem strong_continuous_of_dense_span_of_bounded
    {A : X → E →L[𝕜] F} {b : ι → E} {C : ℝ}
    (hb : Dense (Submodule.span 𝕜 (Set.range b) : Set E))
    (hA : ∀ i, Continuous (fun x => A x (b i)))
    (hC : ∀ x, ‖A x‖ ≤ C) (v : E) :
    Continuous (fun x => A x v) := by
  apply strong_continuous_of_dense_of_bounded hb ?_ hC v
  intro w hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨i, rfl⟩ := hw
      exact hA i
  | zero => simpa only [map_zero] using (continuous_const : Continuous (fun _ : X => (0 : F)))
  | add w z hw hz ihw ihz =>
      have h : Continuous (fun x => A x w + A x z) :=
        Continuous.add (f := fun x => A x w) (g := fun x => A x z) ihw ihz
      simpa only [map_add] using h
  | smul c w hw ihw =>
      have h : Continuous (fun x => c • A x w) :=
        Continuous.const_smul (g := fun x => A x w) ihw c
      simpa only [map_smul] using h

theorem continuous_apply_of_strong_continuous_of_bounded
    {A : X → E →L[𝕜] F} {v : X → E} {C : ℝ}
    (hA : ∀ w, Continuous (fun x => A x w))
    (hC : ∀ x, ‖A x‖ ≤ C) (hv : Continuous v) :
    Continuous (fun x => A x (v x)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  exact tendsto_apply_of_strong_tendsto_of_bounded
    (fun w => (hA w).continuousAt) (Eventually.of_forall hC) hv.continuousAt

theorem strong_continuous_comp_of_bounded
    {A : X → F →L[𝕜] G} {B : X → E →L[𝕜] F} {C : ℝ}
    (hA : ∀ w, Continuous (fun x => A x w))
    (hB : ∀ v, Continuous (fun x => B x v))
    (hC : ∀ x, ‖A x‖ ≤ C) (v : E) :
    Continuous (fun x => ((A x).comp (B x)) v) := by
  exact continuous_apply_of_strong_continuous_of_bounded
    (A := A) (v := fun x => B x v) hA hC (hB v)

theorem isClosed_zero_set_of_strong_continuous
    {A : X → E →L[𝕜] F}
    (hA : ∀ v, Continuous (fun x => A x v)) :
    IsClosed {x | A x = 0} := by
  have heq : {x | A x = 0} = ⋂ v : E, {x | A x v = 0} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro hx v
      simp [hx]
    · intro hx
      ext v
      exact hx v
  rw [heq]
  exact isClosed_iInter fun v => isClosed_eq (hA v) continuous_const

end InvariantProjection

end OAI
