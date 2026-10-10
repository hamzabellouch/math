import OAI.Probability.PosteriorReplicas.Gaussian.GaussianSmallBall
import OAI.Probability.PosteriorReplicas.Geometry.AffineMoments

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Metric EuclideanGeometry Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
lemma infDist_affine_projection [MeasurableSpace E] [BorelSpace E]
    (L : AffineSubspace ℝ E) {p : E} (hp : p ∈ L) (x : E) :
    Metric.infDist x L = ‖L.directionᗮ.orthogonalProjectionOnto x -
      L.directionᗮ.orthogonalProjectionOnto p‖ := by
  conv_lhs => rw [← AffineSubspace.mk'_eq hp]
  rw [PosteriorRegression.infDist_affine_mk', Metric.infDist_eq_iInf]
  simp only [dist_eq_norm]
  change (⨅ y : L.direction, ‖x-p-(y : E)‖) = _
  rw [← L.direction.starProjection_minimal (x-p)]
  rw [← map_sub]
  change ‖x-p-L.direction.starProjection (x-p)‖ = ‖L.directionᗮ.starProjection (x-p)‖
  rw [Submodule.starProjection_orthogonal_val]

lemma gaussian_affine_inverse_moment (L : AffineSubspace ℝ E) [Nonempty L]
    (k : ℕ) (hk : Module.finrank ℝ L.direction + k + 1 ≤ Module.finrank ℝ E)
    {R : ℝ} (hR : 0 < R) :
    (∫⁻ x : E, ENNReal.ofReal ((Metric.infDist x L)⁻¹^k) ∂stdGaussian E) ≤
      ENNReal.ofReal (R⁻¹^k) * (1 + ENNReal.ofReal (Real.exp (R^2/2)) * 2^(k+1)) := by
  obtain ⟨⟨p,hp⟩⟩ := ‹Nonempty L›
  have hdim : k+1 ≤ Module.finrank ℝ L.directionᗮ := by
    have := L.direction.finrank_add_finrank_orthogonal
    omega
  have h := gaussian_inverse_norm_moment (L.directionᗮ.orthogonalProjectionOnto p) k hdim hR
  rw [← gaussian_orthogonalProjectionOnto L.directionᗮ,
    lintegral_map (by fun_prop) (by fun_prop)] at h
  simpa only [infDist_affine_projection L hp] using h

def gaussianMomentConstant (k : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((Real.sqrt k)⁻¹^k) *
    (1 + ENNReal.ofReal (Real.exp ((k : ℝ)/2)) * 2^(k+1))

lemma gaussianMomentConstant_ne_top (k : ℕ) : gaussianMomentConstant k ≠ ∞ := by
  unfold gaussianMomentConstant
  finiteness

lemma gaussianMomentConstant_pos {k : ℕ} (hk : 1 ≤ k) : 0 < gaussianMomentConstant k := by
  unfold gaussianMomentConstant
  have h : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  positivity

lemma gaussian_gram_inverse_moment (k m : ℕ) (hk : 1 ≤ k)
    (hd : k+m ≤ Module.finrank ℝ E) (p : E) :
    (∫⁻ v : Fin m → E,
      ENNReal.ofReal ((Real.sqrt (Matrix.gram ℝ (fun j => v j-p)).det)⁻¹ ^ k)
      ∂Measure.pi (fun _ => stdGaussian E)) ≤ (gaussianMomentConstant k)^m := by
  have h := replica_integral_of_affine_moment (ν := stdGaussian E) k m p (gaussianMomentConstant k) ?_
  · simpa only [PosteriorRegression.replicaWeight_eq_det] using h
  intro L hL hdim
  have hkp : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hb := gaussian_affine_inverse_moment L k (by omega :
    Module.finrank ℝ L.direction + k + 1 ≤ Module.finrank ℝ E) (Real.sqrt_pos.mpr hkp)
  simpa only [gaussianMomentConstant, Real.sq_sqrt hkp.le] using hb

lemma gaussian_gram_inverse_moment_centered (k m : ℕ) (hk : 1 ≤ k)
    (hd : k+m ≤ Module.finrank ℝ E) :
    (∫⁻ v : Fin m → E,
      ENNReal.ofReal ((Real.sqrt (Matrix.gram ℝ v).det)⁻¹ ^ k)
      ∂Measure.pi (fun _ => stdGaussian E)) ≤ (gaussianMomentConstant k)^m := by
  simpa only [sub_zero] using gaussian_gram_inverse_moment k m hk hd (0 : E)

lemma ae_gaussian_columns_independent (m : ℕ) (hm : m ≤ Module.finrank ℝ E) :
    ∀ᵐ v : Fin m → E ∂Measure.pi (fun _ => stdGaussian E), LinearIndependent ℝ v := by
  have h := ae_replica_independent_of_affine_null (ν := stdGaussian E) (0 : E) m ?_
  · simpa only [sub_zero] using h
  intro L hL hdim
  apply stdGaussian_absolutelyContinuous_volume
  apply Measure.addHaar_affineSubspace _ L
  intro htop
  have hr : L.direction = ⊤ := by rw [htop, AffineSubspace.direction_top]
  rw [hr, finrank_top] at hdim
  omega

end PosteriorReplicas
end

end OAI
