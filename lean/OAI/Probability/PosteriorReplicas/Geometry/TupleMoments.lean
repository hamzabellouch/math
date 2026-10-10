import OAI.Probability.PosteriorReplicas.Geometry.AffineMoments
import OAI.Probability.PosteriorReplicas.Measures.PiTools

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

@[fun_prop] lemma continuous_differences {d m : ℕ} : Continuous (@differences d m) := by
  unfold differences
  fun_prop

@[fun_prop] lemma continuous_affineVolume {d m : ℕ} : Continuous (@affineVolume d m) := by
  unfold affineVolume
  apply Real.continuous_sqrt.comp
  apply Continuous.matrix_det
  unfold Matrix.gram
  fun_prop

lemma measurableSet_row_independent {d k : ℕ} :
    MeasurableSet {A : Rows d k | LinearIndependent ℝ A} := by
  have he : {A : Rows d k | LinearIndependent ℝ A} = {A | (rowGram A).det ≠ 0} := by
    ext A
    exact ⟨fun h => (Matrix.posDef_gram_of_linearIndependent h).det_pos.ne',
      fun h => Matrix.linearIndependent_of_det_gram_ne_zero (show (Matrix.gram ℝ A).det ≠ 0 from h)⟩
  rw [he]
  exact (isClosed_eq continuous_rowGram.matrix_det continuous_const).isOpen_compl.measurableSet

lemma measurableSet_affine_independent {d m : ℕ} :
    MeasurableSet {u : Tuple d m | LinearIndependent ℝ (differences u)} :=
  measurableSet_row_independent.preimage continuous_differences.measurable

@[simp] lemma differences_cons {d m : ℕ} (p : Vec d) (v : Fin m → Vec d) :
    differences (Fin.cons p v : Tuple d m) = fun j => v j - p := by
  funext j
  simp only [PosteriorReplicas.differences, Fin.cons_succ, Fin.cons_zero]

lemma ae_base_tuple_full_rank {d m : ℕ} (hd : 3 ≤ d) (hm : m < d) (base : BaseLaw) :
    ∀ᵐ u : Tuple d m ∂Measure.pi (fun _ => base.measure d),
      LinearIndependent ℝ (differences u) := by
  have : NeZero d := ⟨by omega⟩
  rw [ae_pi_cons (base.measure d) measurableSet_affine_independent]
  apply Filter.Eventually.of_forall
  intro p
  simpa only [differences_cons] using
    ae_replica_independent_of_affine_null p m
      (fun L _ hL => base_affine_null hd base L (by omega))

lemma ae_gaussian_rows_full_rank {d k : ℕ} (hd : 3 ≤ d) (hk : k < d) :
    ∀ᵐ A ∂gaussianRows d k, LinearIndependent ℝ A := by
  have h := ae_replica_independent_of_affine_null (ν := stdGaussian (Vec d)) (0 : Vec d) k
    (fun L _ hL => base_affine_null hd .gaussian L (by omega))
  simpa only [sub_zero, gaussianRows] using h

lemma base_tuple_inverse_finite {d k m : ℕ} (hd : k + m + 2 ≤ d) (hm : 1 ≤ m)
    (base : BaseLaw) :
    (∫⁻ u : Tuple d m, (ENNReal.ofReal (affineVolume u))⁻¹ ^ k
      ∂Measure.pi (fun _ => base.measure d)) < ∞ := by
  have : NeZero d := ⟨by omega⟩
  have hrank := ae_base_tuple_full_rank (by omega : 3 ≤ d) (by omega : m < d) base
  have he : (fun u : Tuple d m => (ENNReal.ofReal (affineVolume u))⁻¹ ^ k) =ᵐ[
      Measure.pi (fun _ => base.measure d)]
      (fun u => ENNReal.ofReal ((affineVolume u)⁻¹ ^ k)) := by
    filter_upwards [hrank] with u hu
    have hp : 0 < affineVolume u := Real.sqrt_pos.mpr
      (Matrix.posDef_gram_of_linearIndependent hu).det_pos
    rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_inv_of_pos hp]
  rw [lintegral_congr_ae he,
    lintegral_pi_cons (base.measure d) (by fun_prop)]
  let C : ℝ≥0∞ := 1 + (ENNReal.ofReal (baseProjectionConstant base d (k+1)) * 2^(k+1)) * 2^(k+1)
  have hbound (p : Vec d) :
      (∫⁻ v : Fin m → Vec d, ENNReal.ofReal
        ((affineVolume (Fin.cons p v))⁻¹ ^ k) ∂Measure.pi (fun _ => base.measure d)) ≤ C^m := by
    have h := replica_integral_of_affine_moment k m p C
      (fun L _ hL => base_affine_inverse_bound hd hm base L hL)
    simpa only [PosteriorRegression.replicaWeight_eq_det,
      affineVolume, differences_cons] using h
  apply lt_of_le_of_lt (lintegral_mono hbound)
  simp only [lintegral_const, measure_univ, mul_one]
  dsimp only [C]
  finiteness

lemma gaussian_rows_inverse_finite {d k m : ℕ} (hd : k + m + 2 ≤ d) (hk : 1 ≤ k) :
    (∫⁻ A : Rows d k, ENNReal.ofReal ((Real.sqrt (rowGram A).det)⁻¹ ^ m)
      ∂gaussianRows d k) < ∞ := by
  simpa only [rowGram_eq_gram, sub_zero, BaseLaw.measure, gaussianRows] using
    base_replica_inverse_finite (k := m) (m := k) (by omega) hk .gaussian (0 : Vec d)

lemma base_density_sup_moment_finite {d k m : ℕ} (hd : k + m + 2 ≤ d) (hk : 1 ≤ k)
    (base : BaseLaw) :
    (∫⁻ A : Rows d k, ENNReal.ofReal
      (baseProjectionConstant base d k / Real.sqrt (rowGram A).det) ^ m
      ∂gaussianRows d k) < ∞ := by
  have hc := (baseProjectionConstant_pos (by omega : k < d) base).le
  have he (A : Rows d k) : ENNReal.ofReal
      (baseProjectionConstant base d k / Real.sqrt (rowGram A).det) ^ m =
        ENNReal.ofReal (baseProjectionConstant base d k)^m *
          ENNReal.ofReal ((Real.sqrt (rowGram A).det)⁻¹ ^ m) := by
    rw [div_eq_mul_inv, ENNReal.ofReal_mul hc, mul_pow,
      ENNReal.ofReal_pow (by positivity)]
  simp_rw [he]
  rw [lintegral_const_mul _ (by fun_prop)]
  exact ENNReal.mul_lt_top (by finiteness) (gaussian_rows_inverse_finite hd hk)

end PosteriorReplicas
end

end OAI
