import Mathlib

namespace OAI

noncomputable section

open Filter
open scoped Topology

namespace Problem336
namespace ProjectionLimit

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem cycle_projection_tendsto
    (C : ℕ → Submodule ℝ E) [∀ n, (C n).HasOrthogonalProjection]
    [(⨆ n, C n).topologicalClosure.HasOrthogonalProjection]
    (hC : Monotone C) (x : E) :
    Tendsto (fun n => (C n).starProjection x) atTop
      (𝓝 ((⨆ n, C n).topologicalClosure.starProjection x)) :=
  Submodule.starProjection_tendsto_closure_iSup C hC x

theorem free_kernel_tendsto
    (C : ℕ → Submodule ℝ E) [∀ n, (C n).HasOrthogonalProjection]
    [(⨆ n, C n).topologicalClosure.HasOrthogonalProjection]
    (hC : Monotone C) (Q : ℕ → E → E)
    (hQ : ∀ x, Tendsto (fun n => Q n x) atTop (𝓝 x)) (x : E) :
    Tendsto (fun n => Q n x - (C n).starProjection x) atTop
      (𝓝 (x - (⨆ n, C n).topologicalClosure.starProjection x)) :=
  (hQ x).sub (cycle_projection_tendsto C hC x)

theorem kernel_matrix_tendsto
    {ι : Type*} (K : ℕ → E → E) (Klim : E → E)
    (hK : ∀ x, Tendsto (fun n => K n x) atTop (𝓝 (Klim x)))
    (v : ι → E) :
    Tendsto (fun n => (fun i j => inner ℝ (v i) (K n (v j)) : Matrix ι ι ℝ))
      atTop (𝓝 (fun i j => inner ℝ (v i) (Klim (v j)))) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  exact tendsto_const_nhds.inner (hK (v j))

theorem kernel_minor_tendsto
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : ℕ → E → E) (Klim : E → E)
    (hK : ∀ x, Tendsto (fun n => K n x) atTop (𝓝 (Klim x)))
    (v : ι → E) :
    Tendsto (fun n => Matrix.det (fun i j => inner ℝ (v i) (K n (v j))))
      atTop (𝓝 (Matrix.det (fun i j => inner ℝ (v i) (Klim (v j))))) := by
  exact (continuous_id.matrix_det.tendsto _).comp (kernel_matrix_tendsto K Klim hK v)

theorem free_kernel_minor_tendsto
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : ℕ → Submodule ℝ E) [∀ n, (C n).HasOrthogonalProjection]
    [(⨆ n, C n).topologicalClosure.HasOrthogonalProjection]
    (hC : Monotone C) (Q : ℕ → E → E)
    (hQ : ∀ x, Tendsto (fun n => Q n x) atTop (𝓝 x)) (v : ι → E) :
    Tendsto
      (fun n => Matrix.det
        (fun i j => inner ℝ (v i) (Q n (v j) - (C n).starProjection (v j))))
      atTop
      (𝓝 (Matrix.det (fun i j => inner ℝ (v i)
        (v j - (⨆ n, C n).topologicalClosure.starProjection (v j))))) :=
  kernel_minor_tendsto _ _ (free_kernel_tendsto C hC Q hQ) v

theorem free_kernel_minor_ofReal_tendsto
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : ℕ → Submodule ℝ E) [∀ n, (C n).HasOrthogonalProjection]
    [(⨆ n, C n).topologicalClosure.HasOrthogonalProjection]
    (hC : Monotone C) (Q : ℕ → E → E)
    (hQ : ∀ x, Tendsto (fun n => Q n x) atTop (𝓝 x)) (v : ι → E) :
    Tendsto
      (fun n => ENNReal.ofReal (Matrix.det
        (fun i j => inner ℝ (v i) (Q n (v j) - (C n).starProjection (v j)))))
      atTop
      (𝓝 (ENNReal.ofReal (Matrix.det (fun i j => inner ℝ (v i)
        (v j - (⨆ n, C n).topologicalClosure.starProjection (v j)))))) :=
  ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (free_kernel_minor_tendsto C hC Q hQ v)

theorem projection_kernel_eq_gram
    {ι : Type*} (C : Submodule ℝ E) [C.HasOrthogonalProjection] (v : ι → E) :
    (fun i j => inner ℝ (v i) (C.starProjection (v j))) =
      Matrix.gram ℝ (fun i => C.starProjection (v i)) := by
  funext i j
  change inner ℝ (v i) (C.starProjection (v j)) =
    inner ℝ (C.starProjection (v i)) (C.starProjection (v j))
  rw [C.inner_starProjection_left_eq_right]
  congr 1
  exact (C.starProjection_eq_self_iff.mpr (C.starProjection_apply_mem (v j))).symm

theorem projection_kernel_minor_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Submodule ℝ E) [C.HasOrthogonalProjection] (v : ι → E) :
    0 ≤ Matrix.det (fun i j => inner ℝ (v i) (C.starProjection (v j))) := by
  rw [projection_kernel_eq_gram]
  exact (Matrix.posSemidef_gram ℝ _).det_nonneg

end ProjectionLimit
end Problem336

end

end OAI
