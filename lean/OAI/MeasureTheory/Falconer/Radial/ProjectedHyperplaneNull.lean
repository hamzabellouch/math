import OAI.MeasureTheory.Falconer.Estimates.ProjectedIndependentTuples

namespace OAI

/-! # Independent sampled tuples exclude mass on projected hyperplanes -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d n : ℕ}

theorem orthogonal_independent_square_eq_zero (v : Fin (n+1) → Space (n+1))
    (hv : LinearIndependent ℝ v) (w : Space (n+1))
    (horth : ∀ i, inner ℝ w (v i) = 0) : w = 0 := by
  have hdet : (euclideanColumnMatrix v).det ≠ 0 := by
    intro hd
    have hg := Matrix.det_gram_ne_zero_iff_linearIndependent.mpr hv
    apply hg
    rw [euclideanColumnMatrix_gram,Matrix.det_mul,Matrix.det_transpose,hd,mul_zero]
  exact eq_zero_of_orthogonal_columns v hdet w horth

theorem projected_hyperplane_null_of_tuples (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (P : Space d →L[ℝ] Space (n+1))
    (htuple : ∀ᵐ z : Space d × (Fin (n+1) → Space d) ∂μ.prod (Measure.pi (fun _ => μ)),
      LinearIndependent ℝ (fun i => P (z.2 i-z.1)))
    (w : Space (n+1)) (hw : ‖w‖ = 1) (t : ℝ) :
    (μ.map P) {y | inner ℝ w y = t} = 0 := by
  rw [Measure.map_apply P.continuous.measurable (measurableSet_eq_fun (by fun_prop) measurable_const)]
  let K : Set (Space d) := {x | inner ℝ w (P x) = t}
  change μ K = 0
  by_contra hK
  have hpos : 0 < (μ.prod (Measure.pi (fun _ : Fin (n+1) => μ)))
      (K ×ˢ Set.pi univ (fun _ => K)) := by
    rw [Measure.prod_prod,Measure.pi_pi,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    exact pos_iff_ne_zero.mpr (mul_ne_zero hK (pow_ne_zero _ hK))
  obtain ⟨z,hz,hind⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos.ne'
    (ae_restrict_of_ae htuple)
  have horth (i : Fin (n+1)) : inner ℝ w (P (z.2 i-z.1)) = 0 := by
    rw [map_sub,inner_sub_right]
    exact sub_eq_zero.mpr ((hz.2 i (mem_univ i)).trans hz.1.symm)
  have hzero := orthogonal_independent_square_eq_zero _ hind w horth
  rw [hzero,norm_zero] at hw
  norm_num at hw

theorem gaussian_projected_hyperplanes_null_ae (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (hnull : ∀ p : Space d, ∀ V : Submodule ℝ (Space d), Module.finrank ℝ V ≤ n →
      μ {x | x-p ∈ V} = 0) :
    ∀ᵐ A : Fin (n+1) → Space d ∂gaussianRows d (n+1),
      ∀ w : Space (n+1), ‖w‖ = 1 → ∀ t : ℝ,
        (μ.map (gaussianRowMap A)) {y | inner ℝ w y = t} = 0 := by
  filter_upwards [gaussian_projected_tuple_independent_ae μ hnull] with A hA w hw t
  exact projected_hyperplane_null_of_tuples μ _ hA w hw t

end Falconer

end OAI
