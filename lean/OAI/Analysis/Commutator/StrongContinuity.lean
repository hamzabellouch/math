import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology

open Filter

namespace Kadison.StrongContinuity

variable {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℂ E]

variable (T : X → E →ₗᵢ[ℂ] E)

def vectors : Submodule ℂ E where
  carrier := {x | Continuous (fun g => T g x)}
  zero_mem' := by
    change Continuous (fun g => T g (0:E))
    simpa only [map_zero] using (continuous_const : Continuous (fun _ : X => (0:E)))
  add_mem' := by
    intro x y hx hy
    change Continuous (fun g => T g x) at hx
    change Continuous (fun g => T g y) at hy
    change Continuous (fun g => T g (x+y))
    simp only [map_add]
    exact hx.add hy
  smul_mem' := by
    intro a x hx
    change Continuous (fun g => T g x) at hx
    change Continuous (fun g => T g (a • x))
    simp only [map_smul]
    exact continuous_const.smul hx

lemma isClosed_vectors : IsClosed (vectors T : Set E) := by
  apply IsSeqClosed.isClosed
  intro u x hu hux
  have hl : TendstoUniformly (fun n g => T g (u n)) (fun g => T g x) atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    filter_upwards [Metric.tendsto_nhds.mp hux ε hε] with n hn
    intro g
    simpa only [LinearIsometry.dist_map,dist_comm] using hn
  exact hl.continuous (Eventually.of_forall hu).frequently

lemma of_denseRange {ι : Type*} (v : ι → E) (hd : DenseRange v)
    (hv : ∀ i, Continuous fun g => T g (v i)) (x : E) : Continuous fun g => T g x := by
  have hs : Set.range v ⊆ (vectors T : Set E) := by rintro _ ⟨i,rfl⟩; exact hv i
  have he : (Set.univ : Set E) ⊆ (vectors T : Set E) := by
    rw [← hd.closure_range]
    exact (isClosed_vectors T).closure_subset_iff.mpr hs
  exact he (Set.mem_univ x)

lemma of_total {S : Set E} (hS : (Submodule.span ℂ S).topologicalClosure=⊤)
    (hv : ∀ x ∈ S, Continuous fun g => T g x) (x : E) : Continuous fun g => T g x := by
  have hs : Submodule.span ℂ S ≤ vectors T := Submodule.span_le.mpr hv
  have ht : (Submodule.span ℂ S).topologicalClosure ≤ vectors T :=
    Submodule.topologicalClosure_minimal _ hs (isClosed_vectors T)
  rw [hS] at ht
  exact ht (Submodule.mem_top : x ∈ (⊤ : Submodule ℂ E))

lemma joint (h : ∀ x, Continuous fun g => T g x) : Continuous (fun p : X × E => T p.1 p.2) := by
  apply continuous_prod_of_continuous_lipschitzWith' _ 1
  · intro g
    exact (T g).isometry.lipschitzWith
  · exact h

end Kadison.StrongContinuity

end

end
end

end OAI
