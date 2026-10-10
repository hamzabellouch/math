import OAI.Probability.PosteriorReplicas.Gaussian.GaussianGramMoment

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Metric EuclideanGeometry Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

lemma sphereLaw_closedBall {d : ℕ} [NeZero d] (z : Vec d) {r : ℝ} (hr : 0 < r) :
    sphereLaw d (closedBall z r) ≤ ENNReal.ofReal ((3:ℝ)*4^d) * ENNReal.ofReal (r^(d-1)) := by
  simpa only [sphereLaw, PosteriorRegression.ambientSphereLaw, PosteriorRegression.sphereLaw,
    finrank_euclideanSpace_fin] using
    PosteriorRegression.ambientSphereLaw_closedBall z hr (d-1) (by simp)

lemma sphereLaw_support_unit {d : ℕ} : (sphereLaw d).support ⊆ closedBall 0 1 := by
  exact (PosteriorRegression.ambientSphereLaw_support (E := Vec d)).trans sphere_subset_closedBall

lemma sphere_affine_tube_quantitative {d k : ℕ} [NeZero d]
    (L : AffineSubspace ℝ (Vec d)) [Nonempty L]
    (hd : Module.finrank ℝ L.direction + k ≤ d-1) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    sphereLaw d {x | Metric.infDist x L ≤ r} ≤ ENNReal.ofReal ((72:ℝ)^d) * ENNReal.ofReal (r^k) := by
  classical
  obtain ⟨s,hcard,hcover⟩ := PosteriorRegression.exists_affine_tube_cover L hr hr1
  let c : L.direction → Vec d := fun y => (y : Vec d) + (orthogonalProjection L 0 : Vec d)
  have hsub : {x | Metric.infDist x L ≤ r} ≤ᵐ[sphereLaw d]
      ⋃ y ∈ s, closedBall (c y) (2*r) := by
    filter_upwards [(sphereLaw d).support_mem_ae] with x hx
    intro hdist
    have hxunit : ‖x‖ ≤ 1 := by simpa using sphereLaw_support_unit hx
    obtain ⟨y,hy,hyx⟩ := hcover x hxunit hdist
    exact mem_iUnion₂.mpr ⟨y,hy,hyx⟩
  let a := Module.finrank ℝ L.direction
  have hd0 : 1 ≤ d := NeZero.one_le
  have ha : a ≤ d := by dsimp [a]; omega
  have hpow : (3/r)^a * ((3:ℝ)*4^d) * (2*r)^(d-1) ≤ (72:ℝ)^d*r^k := by
    have hcan : (3/r)^a * ((3:ℝ)*4^d) * (2*r)^(d-1) =
        (3*4^d*3^a*2^(d-1)) * r^(d-1-a) := by
      have hdim : d-1 = a+(d-1-a) := by dsimp [a]; omega
      nth_rw 1 [hdim]
      rw [mul_pow, div_pow, pow_add]
      field_simp
      rw [hdim, pow_add]
      simp only [Nat.add_sub_cancel_left]
      ring
    rw [hcan]
    have hc : (3:ℝ)*4^d*3^a*2^(d-1) ≤ (72:ℝ)^d := by
      have h3 : (3:ℝ) ≤ 3^d := by simpa using pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 3) hd0
      have h3a : (3:ℝ)^a ≤ 3^d := pow_le_pow_right₀ (by norm_num) ha
      have h2 : (2:ℝ)^(d-1) ≤ 2^d := pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
      calc
        _ ≤ 3^d*4^d*3^d*2^d := by gcongr
        _ = (72:ℝ)^d := by simp only [← mul_pow]; congr 1; norm_num
    apply mul_le_mul hc ?_ (by positivity) (by positivity)
    exact pow_le_pow_of_le_one hr.le hr1 (by dsimp [a]; omega)
  calc
    _ ≤ sphereLaw d (⋃ y ∈ s, closedBall (c y) (2*r)) := measure_mono_ae hsub
    _ ≤ ∑ y ∈ s, sphereLaw d (closedBall (c y) (2*r)) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _y ∈ s, ENNReal.ofReal ((3:ℝ)*4^d)*ENNReal.ofReal ((2*r)^(d-1)) := by
      exact Finset.sum_le_sum (fun y _ => sphereLaw_closedBall (c y) (by positivity))
    _ = (s.card : ℝ≥0∞) * (ENNReal.ofReal ((3:ℝ)*4^d)*ENNReal.ofReal ((2*r)^(d-1))) := by simp
    _ ≤ ENNReal.ofReal ((3/r)^a) * (ENNReal.ofReal ((3:ℝ)*4^d)*ENNReal.ofReal ((2*r)^(d-1))) := by
      gcongr
      exact_mod_cast ENNReal.ofReal_le_ofReal hcard
    _ ≤ _ := by
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      nlinarith [hpow]

lemma spherical_tilt_affine_tube {d k : ℕ} [NeZero d]
    {f : Vec d → ℝ≥0∞} {M : ℝ≥0∞} (hfM : ∀ x, f x ≤ M)
    (L : AffineSubspace ℝ (Vec d)) [Nonempty L]
    (hd : Module.finrank ℝ L.direction+k ≤ d-1) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    (sphereLaw d).withDensity f {x | Metric.infDist x L ≤ r} ≤
      (M*ENNReal.ofReal ((72:ℝ)^d)) * ENNReal.ofReal (r^k) := by
  rw [withDensity_apply _ (measurableSet_le (Metric.continuous_infDist_pt _).measurable measurable_const)]
  calc
    _ ≤ ∫⁻ _x in {x | Metric.infDist x L ≤ r}, M ∂sphereLaw d := lintegral_mono hfM
    _ = M * sphereLaw d {x | Metric.infDist x L ≤ r} := by simp
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul' le_rfl (sphere_affine_tube_quantitative L hd hr hr1)

end PosteriorReplicas
end

end OAI
