import OAI.Analysis.KadisonKastler.BicentralizerHilbertProjection

namespace OAI

/-! # Strong continuity of the bicentralizer retraction on bounded nets

The reference-vector projection estimate and the dense commutant orbit
extend convergence to every vector in the original representation.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {ι : Type*} {l : Filter ι}

theorem bicentralizerProjection_strong_tendsto (ξ : H)
    (hsep : Function.Injective (algebraVectorMap M ξ))
    (a : ι → Algebra M) (b : Algebra M) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ i, ‖a i‖ ≤ C)
    (ht : Tendsto (fun i => (a i).val ξ) l (𝓝 (b.val ξ))) (η : H) :
    Tendsto (fun i => (bicentralizerProjectionCLM ξ hsep (a i)).val η) l
      (𝓝 ((bicentralizerProjectionCLM ξ hsep b).val η)) := by
  let E := bicentralizerProjectionCLM ξ hsep
  let T (i : ι) : Algebra M := E (a i-b)
  have hbound : ∀ i, ‖T i‖ ≤ C+‖b‖ := by
    intro i
    exact (bicentralizerProjection_norm_le ξ hsep _).trans
      ((norm_sub_le _ _).trans (add_le_add (ha i) le_rfl))
  have hzero : Tendsto (fun i => (a i-b).val ξ) l (𝓝 0) := by
    change Tendsto (fun i => (a i).val ξ-b.val ξ) l (𝓝 0)
    simpa only [sub_self] using ht.sub_const (b.val ξ)
  have href : Tendsto (fun i => (T i).val ξ) l (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) ?_
      (by simpa only [norm_zero] using hzero.norm)
    exact fun i => bicentralizerProjection_vector_norm_le ξ hsep (a i-b)
  have hall := algebra_strong_tendsto_of_reference ξ
    (commutant_cyclic_of_separating_reference ξ hsep) T (C+‖b‖)
    (add_nonneg hC (norm_nonneg _)) hbound href η
  have he (i : ι) : (T i).val η=(E (a i)).val η-(E b).val η := by
    simp only [T,map_sub,AddSubgroupClass.coe_sub,sub_apply]
  simp only [he] at hall
  exact (tendsto_sub_nhds_zero_iff).mp hall

end

end KadisonKastler

end OAI
