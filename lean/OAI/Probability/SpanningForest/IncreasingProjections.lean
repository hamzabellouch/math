import Mathlib

namespace OAI

noncomputable section

open Filter Topology

namespace Problem336

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

theorem tendsto_starProjection_of_mem_closure_iSup
    (C : ℕ → Submodule 𝕜 E) [∀ n, (C n).HasOrthogonalProjection]
    (hC : Monotone C) {x : E}
    (hx : x ∈ (⨆ n, C n).topologicalClosure) :
    Tendsto (fun n => (C n).starProjection x) atTop (𝓝 x) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hx (ε / 2) (by positivity)
  obtain ⟨N, hyN⟩ := (Submodule.mem_iSup_of_directed C hC.directed_le).mp hy
  refine ⟨N, fun n hn => ?_⟩
  have hyn : y ∈ C n := hC hn hyN
  have hfix : (C n).starProjection y = y :=
    (C n).starProjection_eq_self_iff.mpr hyn
  have hdist : dist ((C n).starProjection x) y ≤ dist x y := by
    simpa only [hfix, NNReal.coe_one, one_mul] using
      (C n).lipschitzWith_starProjection.dist_le_mul x y
  calc
    dist ((C n).starProjection x) x ≤
        dist ((C n).starProjection x) y + dist y x := dist_triangle _ _ _
    _ ≤ dist x y + dist y x := add_le_add hdist le_rfl
    _ < ε := by rw [dist_comm y x]; linarith

theorem tendsto_starProjection_of_closure_iSup_eq
    (C : ℕ → Submodule 𝕜 E) [∀ n, (C n).HasOrthogonalProjection]
    (hC : Monotone C) (D : Submodule 𝕜 E) [D.HasOrthogonalProjection]
    (hD : (⨆ n, C n).topologicalClosure = D) (x : E) :
    Tendsto (fun n => (C n).starProjection x) atTop (𝓝 (D.starProjection x)) := by
  have hCD (n : ℕ) : C n ≤ D := by
    rw [← hD]
    exact (le_iSup C n).trans (Submodule.le_topologicalClosure _)
  have hx : D.starProjection x ∈ (⨆ n, C n).topologicalClosure := by
    rw [hD]
    exact D.starProjection_apply_mem x
  have hconv := tendsto_starProjection_of_mem_closure_iSup C hC hx
  have heq (n : ℕ) : (C n).starProjection (D.starProjection x) =
      (C n).starProjection x := by
    exact congrArg (fun f : E →L[𝕜] E => f x)
      (Submodule.starProjection_comp_starProjection_of_le (hCD n))
  simpa only [heq] using hconv

theorem tendsto_sub_starProjection_of_closure_iSup_eq
    (C : ℕ → Submodule 𝕜 E) [∀ n, (C n).HasOrthogonalProjection]
    (hC : Monotone C) (D : Submodule 𝕜 E) [D.HasOrthogonalProjection]
    (hD : (⨆ n, C n).topologicalClosure = D)
    (Q : ℕ → E →L[𝕜] E)
    (hQ : ∀ x, Tendsto (fun n => Q n x) atTop (𝓝 x)) (x : E) :
    Tendsto (fun n => Q n x - (C n).starProjection x) atTop
      (𝓝 (x - D.starProjection x)) :=
  (hQ x).sub (tendsto_starProjection_of_closure_iSup_eq C hC D hD x)

theorem tendsto_det_sub_starProjection_of_closure_iSup_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : ℕ → Submodule 𝕜 E) [∀ n, (C n).HasOrthogonalProjection]
    (hC : Monotone C) (D : Submodule 𝕜 E) [D.HasOrthogonalProjection]
    (hD : (⨆ n, C n).topologicalClosure = D)
    (Q : ℕ → E →L[𝕜] E)
    (hQ : ∀ x, Tendsto (fun n => Q n x) atTop (𝓝 x)) (v : ι → E) :
    Tendsto (fun n => Matrix.det (fun i j =>
      inner 𝕜 (v i) (Q n (v j) - (C n).starProjection (v j)))) atTop
      (𝓝 (Matrix.det (fun i j => inner 𝕜 (v i) (v j - D.starProjection (v j))))) := by
  have hm : Tendsto (fun n => (fun i j =>
        inner 𝕜 (v i) (Q n (v j) - (C n).starProjection (v j)))) atTop
      (𝓝 (fun i j => inner 𝕜 (v i) (v j - D.starProjection (v j)))) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    exact tendsto_const_nhds.inner
      (tendsto_sub_starProjection_of_closure_iSup_eq C hC D hD Q hQ (v j))
  exact (continuous_id.matrix_det.tendsto _).comp hm

end Problem336

end

end OAI
