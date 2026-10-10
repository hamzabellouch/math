import OAI.Probability.PosteriorReplicas.Gaussian.MatrixNoise
import OAI.Probability.PosteriorReplicas.Gaussian.RandomComplement

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

lemma matrixNormal_density (m k : ℕ) : matrixNormal m k =
    (volume : Measure (Fin m → Fin k → ℝ)).withDensity
      (fun z => ∏ i, ∏ j, gaussianPDF 0 1 (z i j)) := by
  have h := matrixNormal_scale m k 0
  have he : matrixNoiseDensity m k 0 = (fun z => ∏ i, ∏ j, gaussianPDF 0 1 (z i j)) := by
    funext z
    have hv : (⟨(noiseScale 0)^2, sq_nonneg _⟩ : ℝ≥0) = 1 := by ext; norm_num [noiseScale]
    simp only [matrixNoiseDensity, hv]
    rfl
  rw [he] at h
  simpa [noiseScale] using h

lemma matrixNormal_transpose (m k : ℕ) : (matrixNormal m k).map (transposeCLE m k) =
    matrixNormal k m := by
  let e := (transposeCLE m k).toHomeomorph.toMeasurableEquiv
  rw [matrixNormal_density, matrixNormal_density]
  change ((volume : Measure (Fin m → Fin k → ℝ)).withDensity _).map e = _
  rw [map_withDensity_equiv _ e (by fun_prop)]
  change ((volume : Measure (Fin m → Fin k → ℝ)).map (transposeCLE m k)).withDensity _ = _
  rw [(transpose_volume_preserving m k).map_eq]
  congr 1
  funext z
  exact Finset.prod_comm

lemma gaussianRows_eq_matrixNormal (d k : ℕ) : gaussianRows d k =
    (matrixNormal k d).map (fun z i => WithLp.toLp 2 (z i)) := by
  unfold gaussianRows matrixNormal
  rw [Measure.pi_map_pi (fun _ => (WithLp.measurable_toLp _ _).aemeasurable)]
  simp_rw [map_pi_eq_stdGaussian]

def vecTranspose {d k : ℕ} (A : Rows d k) : Rows k d :=
  fun j => WithLp.toLp 2 (fun i => A i j)

@[fun_prop] lemma measurable_vecTranspose {d k : ℕ} : Measurable (@vecTranspose d k) := by
  unfold vecTranspose
  fun_prop

@[simp] lemma vecTranspose_involutive {d k : ℕ} (A : Rows d k) :
    vecTranspose (vecTranspose A) = A := rfl

lemma gaussianRows_transpose (d k : ℕ) : (gaussianRows d k).map vecTranspose = gaussianRows k d := by
  rw [gaussianRows_eq_matrixNormal d k, Measure.map_map (by fun_prop) (by fun_prop),
    gaussianRows_eq_matrixNormal k d, ← matrixNormal_transpose k d,
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

def rowMix {d ℓ k : ℕ} (C : Rows ℓ k) (A : Rows d ℓ) : Rows d k :=
  fun i => ∑ j, (C i j) • A j

@[fun_prop] lemma measurable_rowMix {d ℓ k : ℕ} :
    Measurable (fun z : Rows ℓ k × Rows d ℓ => rowMix z.1 z.2) := by
  unfold rowMix
  fun_prop

lemma rowMix_apply {d ℓ k : ℕ} (C : Rows ℓ k) (A : Rows d ℓ) (i : Fin k) (j : Fin d) :
    rowMix C A i j = ⟪C i, vecTranspose A j⟫ := by
  simp [rowMix, vecTranspose, PiLp.inner_apply, Finset.sum_apply, mul_comm]

lemma gaussianRows_mix {d ℓ k : ℕ} {C : Rows ℓ k} (hC : Orthonormal ℝ C) :
    (gaussianRows d ℓ).map (rowMix C) = gaussianRows d k := by
  have hc : (stdGaussian (Vec ℓ)).map (fun x => WithLp.toLp 2 (labels C x)) = stdGaussian (Vec k) := by
    change ((stdGaussian (Vec ℓ)).map ((WithLp.toLp 2) ∘ labels C)) = _
    rw [← Measure.map_map (WithLp.measurable_toLp _ _) (show Measurable (labels C) by fun_prop)]
    change ((stdGaussian (Vec ℓ)).map (fun x i => ⟪C i, x⟫)).map (WithLp.toLp 2) = _
    rw [PosteriorRegression.orthonormal_gaussian_map hC, map_pi_eq_stdGaussian]
  have hm : (gaussianRows ℓ d).map (fun v i => WithLp.toLp 2 (labels C (v i))) = gaussianRows k d := by
    unfold gaussianRows
    rw [Measure.pi_map_pi (f := fun _ : Fin d => fun x : Vec ℓ => WithLp.toLp 2 (labels C x))
      (fun _ => by fun_prop)]
    simp_rw [hc]
  have h := congrArg (Measure.map (@vecTranspose k d)) hm
  rw [Measure.map_map (by fun_prop) (by fun_prop), gaussianRows_transpose] at h
  rw [← gaussianRows_transpose d ℓ, Measure.map_map (by fun_prop) (by fun_prop)] at h
  convert h using 1
  congr 1
  funext A i
  ext j
  exact rowMix_apply C A i j

lemma rowMix_starProjection {d ℓ k : ℕ} (C : Rows ℓ k) (A : Rows d ℓ)
    (U : Submodule ℝ (Vec d)) :
    rowMix C (fun j => U.starProjection (A j)) = fun i => U.starProjection (rowMix C A i) := by
  ext i
  simp [rowMix, map_sum]

lemma gaussianRows_mix_projected {d ℓ k : ℕ} {C : Rows ℓ k} (hC : Orthonormal ℝ C)
    (U : Submodule ℝ (Vec d)) :
    (gaussianRows d ℓ).map (fun A => rowMix C (fun j => U.starProjection (A j))) =
      (gaussianRows d k).map (fun A i => U.starProjection (A i)) := by
  rw [← gaussianRows_mix hC, Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext A
  exact rowMix_starProjection C A U

end PosteriorReplicas
end

end OAI
