import OAI.Probability.PosteriorReplicas.Gaussian.GaussianLogMoment
import OAI.Probability.PosteriorReplicas.Geometry.BaseFunProp

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

@[fun_prop] lemma measurable_gramSchmidtNormed {n : ℕ} (i : Fin n) :
    Measurable (fun v : Fin n → E => gramSchmidtNormed ℝ v i) := by
  unfold gramSchmidtNormed
  exact ((PosteriorRegression.measurable_gramSchmidt i).norm.inv).smul
    (PosteriorRegression.measurable_gramSchmidt i)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma gramSchmidtNormed_mem [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {n : ℕ} (U : Submodule ℝ E) (v : Fin n → E)
    (hv : ∀ i, v i ∈ U) (i : Fin n) : gramSchmidtNormed ℝ v i ∈ U := by
  have hs : Submodule.span ℝ (range v) ≤ U := Submodule.span_le.mpr (by
    rintro _ ⟨j,rfl⟩
    exact hv j)
  apply hs
  rw [← span_gramSchmidt ℝ v, ← span_gramSchmidtNormed_range]
  exact Submodule.subset_span (mem_range_self i)

lemma ae_gaussian_projected_columns_independent (U : Submodule ℝ E) (n : ℕ)
    (hn : n ≤ Module.finrank ℝ U) :
    ∀ᵐ v : Fin n → E ∂Measure.pi (fun _ => stdGaussian E),
      LinearIndependent ℝ (fun i => U.starProjection (v i)) := by
  have hmap : (Measure.pi (fun _ : Fin n => stdGaussian E)).map
      (fun v i => U.orthogonalProjectionOnto (v i)) = Measure.pi (fun _ : Fin n => stdGaussian U) := by
    rw [Measure.pi_map_pi (fun _ => by fun_prop)]
    simp_rw [gaussian_orthogonalProjectionOnto]
  have h := ae_gaussian_columns_independent (E := U) n hn
  rw [← hmap] at h
  have hz : ∀ᵐ v : Fin n → E ∂Measure.pi (fun _ => stdGaussian E),
      LinearIndependent ℝ (fun i => U.orthogonalProjectionOnto (v i)) :=
    (ae_map_iff (f := fun v : Fin n → E => fun i => U.orthogonalProjectionOnto (v i))
      ((Measurable.of_eval (fun i => U.orthogonalProjectionOnto.continuous.measurable.comp
        (measurable_pi_apply i))).aemeasurable) isOpen_setOfPred_linearIndependent.measurableSet).mp h
  filter_upwards [hz] with v hv
  exact hv.map' U.subtype (LinearMap.ker_eq_bot.mpr U.injective_subtype)

def randomComplement {ℓ m k : ℕ} (V : Rows ℓ m) (e : Rows ℓ k) : Rows ℓ k :=
  gramSchmidtNormed ℝ (fun i => kernelComponent V (e i))

@[fun_prop] lemma measurable_randomComplement {ℓ m k : ℕ} :
    Measurable (fun z : Rows ℓ m × Rows ℓ k => randomComplement z.1 z.2) := by
  unfold randomComplement
  apply Measurable.of_eval
  intro i
  exact (measurable_gramSchmidtNormed i).comp (by fun_prop)

lemma randomComplement_orthogonal {ℓ m k : ℕ} {V : Rows ℓ m}
    (hV : LinearIndependent ℝ V) (e : Rows ℓ k) (i : Fin k) (j : Fin m) :
    ⟪randomComplement V e i, V j⟫ = 0 := by
  apply (Submodule.mem_orthogonal' (Submodule.span ℝ (range V))
    (randomComplement V e i)).mp ?_ (V j) (Submodule.subset_span (mem_range_self j))
  unfold randomComplement
  apply gramSchmidtNormed_mem
  intro a
  rw [kernelComponent_eq_starProjection hV]
  exact Submodule.starProjection_apply_mem _ _

lemma ae_randomComplement_orthonormal {ℓ m k : ℕ} {V : Rows ℓ m}
    (hV : LinearIndependent ℝ V) (hkm : k+m ≤ ℓ) :
    ∀ᵐ e ∂gaussianRows ℓ k, Orthonormal ℝ (randomComplement V e) := by
  let U := (Submodule.span ℝ (range V))ᗮ
  have hdim : k ≤ Module.finrank ℝ U := by
    have h := (Submodule.span ℝ (range V)).finrank_add_finrank_orthogonal
    rw [finrank_euclideanSpace, finrank_span_eq_card hV, Fintype.card_fin] at h
    simp only [Fintype.card_fin] at h
    dsimp [U]
    omega
  filter_upwards [ae_gaussian_projected_columns_independent U k hdim] with e he
  apply gramSchmidtNormed_orthonormal
  simpa only [kernelComponent_eq_starProjection hV] using he

end PosteriorReplicas
end

end OAI
