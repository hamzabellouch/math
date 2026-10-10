import OAI.Analysis.TriangularHilbert.TraceWeights

namespace OAI

universe uι

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory Filter
open scoped BigOperators Topology Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section

lemma weight_integrable_center (h u σ : ℝ) (hσ : 0 ≤ σ) :
    Integrable (fun p => weight h u p σ) := by
  exact ((volume.measurePreserving_sub_left u).integrable_comp_of_integrable (density_integrable hσ)).const_mul h

lemma integral_weight_center (h u : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    (∫ p, weight h u p σ) = h := by
  unfold weight
  rw [integral_const_mul,integral_sub_left_eq_self,integral_density hσ,mul_one]

lemma chart_integrable_iff (f : (Three → ℝ) → ℝ) (i j : Three) (d : ℝ) :
    Integrable (fun z : ℝ×ℝ => f (chart i d z)) ↔
      Integrable (fun z : ℝ×ℝ => f (chart j d z)) := by
  have hi k : Integrable (fun z : ℝ×ℝ => f (chart k d z)) ↔
      Integrable (fun z : ℝ×ℝ => f (chart 2 d z)) := by
    simp_rw [chartChange_eq k d]
    exact (chartChange_preserving k d).integrable_comp_emb (chartChange k d).measurableEmbedding (g := fun z : ℝ×ℝ => f (chart 2 d z))
  exact (hi i).trans (hi j).symm

lemma weight_pair_integrable (h a b d : ℝ) (σ : Three → ℝ) (hσ : ∀ v, 0 < σ v) (v k : Three) :
    Integrable (fun z : ℝ×ℝ => weight h a (chart k d z v) (σ v) *
      weight h b (chart k d z (v+1)) (σ (v+1))) := by
  apply (chart_integrable_iff (fun p => weight h a (p v) (σ v)*weight h b (p (v+1)) (σ (v+1))) (v+2) k d).mp
  change Integrable (fun z : ℝ×ℝ => weight h a (chart (v+2) d z v) (σ v)*weight h b (chart (v+2) d z (v+1)) (σ (v+1))) (volume.prod volume)
  fin_cases v
  · simpa [chart] using (weight_integrable_center h a (σ 0) (hσ 0).le).mul_prod
      (weight_integrable_center h b (σ 1) (hσ 1).le)
  · simpa [chart] using (weight_integrable_center h a (σ 1) (hσ 1).le).mul_prod
      (weight_integrable_center h b (σ 2) (hσ 2).le)
  · simpa [chart,mul_comm] using (weight_integrable_center h b (σ 0) (hσ 0).le).mul_prod
      (weight_integrable_center h a (σ 2) (hσ 2).le)

lemma integral_weight_pair (h a b d : ℝ) (σ : Three → ℝ) (hσ : ∀ v, 0 < σ v) (v : Three) :
    planeIntegral (fun p => weight h a (p v) (σ v)*weight h b (p (v+1)) (σ (v+1))) d = h^2 := by
  rw [planeIntegral_eq _ (v+2)]
  change (∫ z : ℝ×ℝ, weight h a (chart (v+2) d z v) (σ v)*weight h b (chart (v+2) d z (v+1)) (σ (v+1)) ∂volume.prod volume) = h^2
  have hp (a b σ τ : ℝ) (hσ : 0 < σ) (hτ : 0 < τ) :
      (∫ z : ℝ×ℝ, weight h a z.1 σ * weight h b z.2 τ ∂volume.prod volume) = h^2 := by
    rw [integral_prod_mul (fun p => weight h a p σ) (fun p => weight h b p τ),
      integral_weight_center h a hσ,integral_weight_center h b hτ,pow_two]
  fin_cases v
  · simpa [chart] using hp a b (σ 0) (σ 1) (hσ 0) (hσ 1)
  · simpa [chart] using hp a b (σ 1) (σ 2) (hσ 1) (hσ 2)
  · simpa [chart,mul_comm] using hp b a (σ 0) (σ 2) (hσ 0) (hσ 2)

variable {ι : Type uι} [Fintype ι]

def edgeCubic (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (p σ : Three → ℝ) (v : Three) : ℝ :=
  ∑ i, ∑ j, ‖A v i j‖^3 * (heatWeights h u p σ v i*heatWeights h u p σ (v+1) j)

lemma edgeCubic_integrable (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (d : ℝ)
    (σ : Three → ℝ) (hσ : ∀ v, 0 < σ v) (v k : Three) :
    Integrable (fun z : ℝ×ℝ => edgeCubic A h u (chart k d z) σ v) := by
  exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    (weight_pair_integrable h (u i) (u j) d σ hσ v k).const_mul _))

lemma planeIntegral_edgeCubic (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (d : ℝ)
    (σ : Three → ℝ) (hσ : ∀ v, 0 < σ v) (v : Three) :
    planeIntegral (fun p => edgeCubic A h u p σ v) d = ∑ i, ∑ j, h^2 * ‖A v i j‖^3 := by
  unfold planeIntegral edgeCubic heatWeights
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    (weight_pair_integrable h (u i) (u j) d σ hσ v 2).const_mul _))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => (weight_pair_integrable h (u i) (u j) d σ hσ v 2).const_mul _)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul]
  change ‖A v i j‖^3 * planeIntegral (fun p => weight h (u i) (p v) (σ v)*weight h (u j) (p (v+1)) (σ (v+1))) d = _
  rw [integral_weight_pair h (u i) (u j) d σ hσ v,mul_comm]
end
end TriangularHilbert.Heat
end

end OAI
