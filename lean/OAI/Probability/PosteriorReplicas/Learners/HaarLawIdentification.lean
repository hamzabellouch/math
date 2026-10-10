import OAI.Probability.PosteriorReplicas.Information.HaarInformationEq

namespace OAI

open MeasureTheory ProbabilityTheory Set InnerProductSpace
open scoped RealInnerProductSpace
noncomputable section
namespace PosteriorReplicas

lemma gramSchmidt_linearIsometry {d ℓ : ℕ} (e : Vec d ≃ₗᵢ[ℝ] Vec d)
    (A : Rows d ℓ) (i : Fin ℓ) :
    gramSchmidt ℝ (fun j => e (A j)) i = e (gramSchmidt ℝ A i) := by
  induction i using WellFoundedLT.induction with
  | ind i hi =>
    rw [gramSchmidt_def, gramSchmidt_def, map_sub, map_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    have hj : j < i := Finset.mem_Iio.mp hj
    rw [hi j hj, Submodule.starProjection_singleton, Submodule.starProjection_singleton,
      e.inner_map_map, e.norm_map, map_smul]

lemma gramSchmidtNormed_linearIsometry {d ℓ : ℕ} (e : Vec d ≃ₗᵢ[ℝ] Vec d)
    (A : Rows d ℓ) :
    gramSchmidtNormed ℝ (fun j => e (A j)) = fun j => e (gramSchmidtNormed ℝ A j) := by
  funext j
  simp only [gramSchmidtNormed, gramSchmidt_linearIsometry, e.norm_map, map_smul]

lemma gaussianRows_orthogonal_invariant {d ℓ : ℕ} (e : Vec d ≃ₗᵢ[ℝ] Vec d) :
    (gaussianRows d ℓ).map (fun A i => e (A i)) = gaussianRows d ℓ := by
  unfold gaussianRows
  rw [Measure.pi_map_pi (fun _ => e.continuous.measurable.aemeasurable)]
  simp only [stdGaussian_map]

lemma haarRows_orthogonal_invariant {d ℓ : ℕ} (e : Vec d ≃ₗᵢ[ℝ] Vec d) :
    (haarRows d ℓ).map (fun A i => e (A i)) = haarRows d ℓ := by
  have hm : Measurable (fun A : Rows d ℓ => fun i => e (A i)) := by fun_prop
  rw [haarRows, Measure.map_map hm measurable_gramSchmidtNormed_rows]
  have he : (fun A : Rows d ℓ => fun i => e (gramSchmidtNormed ℝ A i)) =
      (fun A => gramSchmidtNormed ℝ (fun i => e (A i))) := by
    funext A
    exact (gramSchmidtNormed_linearIsometry e A).symm
  change (gaussianRows d ℓ).map (fun A => fun i => e (gramSchmidtNormed ℝ A i)) = _
  rw [he]
  change (gaussianRows d ℓ).map ((gramSchmidtNormed ℝ) ∘ (fun A i => e (A i))) = _
  rw [← Measure.map_map measurable_gramSchmidtNormed_rows hm,
    gaussianRows_orthogonal_invariant]

lemma haarRows_ae_orthonormal {d ℓ : ℕ} (hℓ : ℓ ≤ d) :
    ∀ᵐ A ∂haarRows d ℓ, Orthonormal ℝ A := by
  have hmeas : MeasurableSet {A : Rows d ℓ | Orthonormal ℝ A} := by
    simp only [orthonormal_iff_ite, ofPred_forall]
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
      measurableSet_eq_fun (by fun_prop) measurable_const
  rw [haarRows]
  apply (ae_map_iff measurable_gramSchmidtNormed_rows.aemeasurable hmeas).mpr
  have hfull := ae_gaussian_columns_independent (E := Vec d) ℓ (by simpa using hℓ)
  filter_upwards [hfull] with A hA
  exact gramSchmidtNormed_orthonormal hA

end PosteriorReplicas
end

end OAI
