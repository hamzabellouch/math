import OAI.Geometry.Relativity.CKS.CollarMetricComparison

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix Set
open scoped Matrix.Norms.Elementwise

lemma quadratic3_vector_smul (g : AmbientMat) (v : Fin 3 → ℝ) (c : ℝ) :
    quadratic3 g (c • v)=c^2*quadratic3 g v := by
  simp only [quadratic3,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ring

lemma quadratic3_positive {g : AmbientMat} (hg : g.PosDef) {v : Fin 3 → ℝ} (hv : v ≠ 0) :
    0 < quadratic3 g v := by
  rw [quadratic3_eq_dot]
  exact hg.dotProduct_mulVec_pos hv

lemma quadratic3_continuous_euclidean : Continuous (fun p : AmbientMat × EuclideanSpace ℝ (Fin 3) =>
    quadratic3 p.1 p.2) := by
  unfold quadratic3
  fun_prop

theorem compact_positive_quadratic_lower {K : Set AmbientMat} (hK : IsCompact K)
    (hpos : ∀ g ∈ K, g.PosDef) :
    ∃ κ : ℝ, 0<κ ∧ ∀ g ∈ K, ∀ v : Fin 3 → ℝ, κ*(∑ i, (v i)^2) ≤ quadratic3 g v := by
  let S : Set (EuclideanSpace ℝ (Fin 3)) := Metric.sphere 0 1
  have hS : IsCompact S := isCompact_sphere 0 1
  have hpositive : ∀ p ∈ K ×ˢ S, 0 < quadratic3 p.1 p.2 := by
    intro p hp
    apply quadratic3_positive (hpos p.1 hp.1)
    intro hz
    have he : p.2=0 := by ext i; exact congrFun hz i
    have hn : ‖p.2‖=1 := by simpa only [S,Metric.mem_sphere,dist_zero_right] using hp.2
    simp [he] at hn
  obtain ⟨κ,hκ,hbound⟩ := (hK.prod hS).exists_forall_le' quadratic3_continuous_euclidean.continuousOn hpositive
  refine ⟨κ,hκ,?_⟩
  intro g hg v
  let V : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 v
  have hvnorm : ‖V‖^2=∑ i, (v i)^2 := EuclideanSpace.real_norm_sq_eq V
  by_cases hv : V=0
  · have hz : v=0 := by ext i; exact congrArg (fun q : EuclideanSpace ℝ (Fin 3) => q i) hv
    simp [hz,quadratic3]
  · have hn : ‖V‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    have hunit : ‖V‖⁻¹ • V ∈ S := by
      simp only [S,Metric.mem_sphere,dist_zero_right,norm_smul,Real.norm_eq_abs,
        abs_inv,abs_norm,inv_mul_cancel₀ hn]
    have hh := hbound (g,‖V‖⁻¹ • V) ⟨hg,hunit⟩
    change κ ≤ quadratic3 g (‖V‖⁻¹ • v) at hh
    rw [quadratic3_vector_smul] at hh
    have hh' := mul_le_mul_of_nonneg_left hh (sq_nonneg ‖V‖)
    have he : ‖V‖^2*((‖V‖⁻¹)^2*quadratic3 g v)=quadratic3 g v := by field_simp
    rw [he, hvnorm] at hh'
    simpa only [mul_comm] using hh'

lemma background_positive {q : Mat} (hq : q.PosDef) : (metricBlock 1 0 q).PosDef := by
  have hh := foliationMetric_posDef (U := (1:ℝ)) (by norm_num) hq (0:Point)
  simpa [foliationMetric,Pi.zero_def] using hh

theorem compact_background_lower {K : Set Mat} (hK : IsCompact K) (hpos : ∀ q ∈ K, q.PosDef) :
    ∃ κ : ℝ, 0<κ ∧ ∀ q ∈ K, ∀ v : Fin 3 → ℝ,
      κ*(∑ i, (v i)^2) ≤ quadratic3 (metricBlock 1 0 q) v := by
  have hc : Continuous (fun q : Mat => metricBlock 1 0 q) := by
    unfold metricBlock
    fun_prop
  obtain ⟨κ,hκ,hh⟩ := compact_positive_quadratic_lower (hK.image hc)
    (by rintro _ ⟨q,hq,rfl⟩; exact background_positive (hpos q hq))
  exact ⟨κ,hκ,fun q hq => hh _ ⟨q,hq,rfl⟩⟩

end
end CKSAngularGeometry

end

end OAI
