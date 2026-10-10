import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped Topology

namespace Kadison

variable {H G : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

lemma strong_tendsto_of_dense_tests {ι κ : Type*} {l : Filter ι}
    (v : κ → H) (hv : DenseRange v) (T : ι → H →L[ℂ] G) (A : H →L[ℂ] G)
    (hT : ∀ i,‖T i‖≤1) (hA : ‖A‖≤1)
    (ht : ∀ j,Tendsto (fun i => T i (v j)) l (𝓝 (A (v j)))) :
    ∀ ξ,Tendsto (fun i => T i ξ) l (𝓝 (A ξ)) := by
  intro ξ
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨j,hj⟩ := Metric.denseRange_iff.mp hv ξ (ε/4) (by positivity)
  have hs : ‖ξ-v j‖<ε/4 := by simpa only [dist_eq_norm,norm_sub_rev] using hj
  have he := Metric.tendsto_nhds.mp (ht j) (ε/2) (by positivity)
  filter_upwards [he] with i hi
  rw [dist_eq_norm] at hi ⊢
  have h1 : ‖T i (ξ-v j)‖≤‖ξ-v j‖ :=
    ((T i).le_opNorm _).trans (by simpa using mul_le_mul_of_nonneg_right (hT i) (norm_nonneg (ξ-v j)))
  have h2 : ‖A (v j-ξ)‖≤‖ξ-v j‖ :=
    (A.le_opNorm _).trans (by simpa only [one_mul,norm_sub_rev] using
      mul_le_mul_of_nonneg_right hA (norm_nonneg (v j-ξ)))
  have hid : T i ξ-A ξ=T i (ξ-v j)+(T i (v j)-A (v j))+A (v j-ξ) := by
    simp only [map_sub]
    abel
  rw [hid]
  exact (norm_add_le _ _).trans_lt (by
    have hn := norm_add_le (T i (ξ-v j)) (T i (v j)-A (v j))
    linarith)

end Kadison

end

end
end

end OAI
