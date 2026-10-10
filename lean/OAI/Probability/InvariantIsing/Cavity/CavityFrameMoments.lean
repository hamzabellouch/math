import OAI.Probability.InvariantIsing.Cavity.CavitySphereMoments

namespace OAI

/-! Uniform even moments for the whole fresh-frame projection vector. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace InvariantIsing

def cavityHaarProjections {n q : ℕ} (v : EuclideanSpace ℝ (Fin n))
    (u : Fin q → EuclideanSpace ℝ (Fin n)) (U : Orthogonal n) : EuclideanSpace ℝ (Fin q) :=
  WithLp.toLp 2 (fun j => ⟪v, matrixRotation U (u j)⟫)

lemma continuous_cavityHaarProjections {n q : ℕ} (v : EuclideanSpace ℝ (Fin n))
    (u : Fin q → EuclideanSpace ℝ (Fin n)) : Continuous (cavityHaarProjections v u) := by
  have hpi : Continuous (fun U : Orthogonal n => fun j : Fin q =>
      ⟪v, matrixRotation U (u j)⟫) := by
    apply continuous_pi
    intro j
    simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial,
      matrixRotation_apply]
    apply continuous_finsetSum
    intro i _
    apply Continuous.mul _ continuous_const
    apply continuous_finsetSum
    intro l _
    exact (continuous_subtype_val.matrix_elem i l).mul continuous_const
  exact (PiLp.continuous_toLp 2 _).comp hpi

lemma cavityHaarProjections_norm_bound {n q : ℕ} (v : EuclideanSpace ℝ (Fin n))
    (u : Fin q → EuclideanSpace ℝ (Fin n)) (U : Orthogonal n) :
    ‖cavityHaarProjections v u U‖ ≤ 1 + ∑ j, (‖v‖ * ‖u j‖) ^ 2 := by
  have hs : ‖cavityHaarProjections v u U‖ ^ 2 ≤ ∑ j, (‖v‖ * ‖u j‖) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_le_sum
    intro j _
    change ⟪v, matrixRotation U (u j)⟫ ^ 2 ≤ (‖v‖ * ‖u j‖) ^ 2
    have h := abs_real_inner_le_norm v (matrixRotation U (u j))
    rw [(matrixRotation U).norm_map] at h
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h 2
  nlinarith [sq_nonneg (‖cavityHaarProjections v u U‖ - 1)]

lemma integrable_cavityHaarProjections_power {n q : ℕ}
    (μ : Measure (Orthogonal n)) [IsFiniteMeasure μ]
    (v : EuclideanSpace ℝ (Fin n)) (u : Fin q → EuclideanSpace ℝ (Fin n)) (p : ℕ) :
    Integrable (fun U => ‖cavityHaarProjections v u U‖ ^ p) μ := by
  apply Integrable.of_bound ((continuous_cavityHaarProjections v u).norm.pow p).aestronglyMeasurable
    ((1 + ∑ j, (‖v‖ * ‖u j‖) ^ 2) ^ p)
  exact ae_of_all _ (fun U => by
    change |‖cavityHaarProjections v u U‖ ^ p| ≤ _
    rw [abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (cavityHaarProjections_norm_bound v u U) p)

lemma cavity_projection_power_le {n q : ℕ} (v : EuclideanSpace ℝ (Fin n))
    (u : Fin q → EuclideanSpace ℝ (Fin n)) (U : Orthogonal n) (k : ℕ) :
    ‖cavityHaarProjections v u U‖ ^ (2 * (k + 1)) ≤
      (q : ℝ) ^ k * ∑ j, |⟪v, matrixRotation U (u j)⟫| ^ (2 * (k + 1)) := by
  rw [pow_mul, EuclideanSpace.real_norm_sq_eq]
  simpa only [cavityHaarProjections, PiLp.toLp_apply, Finset.card_univ, Fintype.card_fin,
    pow_mul, sq_abs] using
    (pow_sum_le_card_mul_sum_pow (s := Finset.univ)
      (f := fun j => ⟪v, matrixRotation U (u j)⟫ ^ 2) (fun _ _ => sq_nonneg _) k)

theorem cavity_frame_even_moment_bound {n q : ℕ} (hn : 0 < n)
    (μ : Measure (Orthogonal n)) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (v : EuclideanSpace ℝ (Fin n)) (u : Fin q → EuclideanSpace ℝ (Fin n))
    (hu : ∀ j, ‖u j‖ = 1) (k : ℕ) :
    (∫ U, ‖cavityHaarProjections v u U‖ ^ (2 * (k + 1)) ∂μ) ≤
      (q : ℝ) ^ (k + 1) * cavityGaussianAbsMoment (2 * (k + 1)) *
        ‖v‖ ^ (2 * (k + 1)) / (n : ℝ) ^ (k + 1) := by
  let p := 2 * (k + 1)
  have hc (j : Fin q) : Continuous (fun U : Orthogonal n => |⟪v, matrixRotation U (u j)⟫| ^ p) :=
    (continuous_const.inner ((continuous_cavityRotationAction n).comp
      (continuous_id.prodMk continuous_const))).abs.pow p
  have hb (j : Fin q) (U : Orthogonal n) :
      |⟪v, matrixRotation U (u j)⟫| ^ p ≤ ‖v‖ ^ p := by
    apply pow_le_pow_left₀ (abs_nonneg _)
    simpa only [(matrixRotation U).norm_map, hu, mul_one] using
      abs_real_inner_le_norm v (matrixRotation U (u j))
  have hi (j : Fin q) : Integrable (fun U : Orthogonal n => |⟪v, matrixRotation U (u j)⟫| ^ p) μ :=
    Integrable.of_bound (hc j).aestronglyMeasurable (‖v‖ ^ p)
      (ae_of_all _ (fun U => by simpa only [Real.norm_eq_abs,
        abs_pow, abs_abs] using hb j U))
  calc
    _ ≤ ∫ U, (q : ℝ) ^ k * ∑ j, |⟪v, matrixRotation U (u j)⟫| ^ p ∂μ := by
      apply integral_mono_of_nonneg
        (ae_of_all _ (fun _ => pow_nonneg (norm_nonneg _) _))
        ((integrable_finsetSum _ (fun j _ => hi j)).const_mul _)
      exact ae_of_all _ (fun U => cavity_projection_power_le v u U k)
    _ = (q : ℝ) ^ k * ∑ j, ∫ U, |⟪v, matrixRotation U (u j)⟫| ^ p ∂μ := by
      rw [integral_const_mul, integral_finsetSum _ (fun j _ => hi j)]
    _ ≤ (q : ℝ) ^ k * ∑ _j : Fin q,
        (cavityGaussianAbsMoment p * ‖v‖ ^ p / (n : ℝ) ^ (k + 1)) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg (Nat.cast_nonneg _) _)
      exact Finset.sum_le_sum (fun j _ => cavity_sphere_even_moment_bound hn μ v (u j) (hu j) (k + 1))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, p]; ring

theorem cavity_frame_even_moment_bound_of_norm {n q : ℕ} (hn : 0 < n)
    (μ : Measure (Orthogonal n)) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (v : EuclideanSpace ℝ (Fin n)) (u : Fin q → EuclideanSpace ℝ (Fin n))
    (hu : ∀ j, ‖u j‖ = 1) (k : ℕ) (L : ℝ) (hv : ‖v‖ ^ 2 ≤ L * n) :
    (∫ U, ‖cavityHaarProjections v u U‖ ^ (2 * (k + 1)) ∂μ) ≤
      (q : ℝ) ^ (k + 1) * cavityGaussianAbsMoment (2 * (k + 1)) * L ^ (k + 1) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hratio : ‖v‖ ^ 2 / (n : ℝ) ≤ L := (div_le_iff₀ hn').mpr hv
  calc
    _ ≤ (q : ℝ) ^ (k + 1) * cavityGaussianAbsMoment (2 * (k + 1)) *
        ‖v‖ ^ (2 * (k + 1)) / (n : ℝ) ^ (k + 1) :=
      cavity_frame_even_moment_bound hn μ v u hu k
    _ = ((q : ℝ) ^ (k + 1) * cavityGaussianAbsMoment (2 * (k + 1))) *
        (‖v‖ ^ 2 / (n : ℝ)) ^ (k + 1) := by rw [div_pow, pow_mul]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (div_nonneg (sq_nonneg _) hn'.le) hratio _)
      (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (cavityGaussianAbsMoment_nonneg _))

theorem cavity_frame_mixture_even_moment {n q : ℕ} {X : Type*} [Fintype X]
    (hn : 0 < n) (μ : Measure (Orthogonal n))
    [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (hsum : ∑ x, w x = 1)
    (v : X → EuclideanSpace ℝ (Fin n)) (u : Fin q → EuclideanSpace ℝ (Fin n))
    (hu : ∀ j, ‖u j‖ = 1) (k : ℕ) (L : ℝ) (hv : ∀ x, ‖v x‖ ^ 2 ≤ L * n) :
    (∫ U, ∑ x, w x * ‖cavityHaarProjections (v x) u U‖ ^ (2 * (k + 1)) ∂μ) ≤
      (q : ℝ) ^ (k + 1) * cavityGaussianAbsMoment (2 * (k + 1)) * L ^ (k + 1) := by
  rw [integral_finsetSum _ (fun x _ =>
    (integrable_cavityHaarProjections_power μ (v x) u _).const_mul (w x))]
  simp_rw [integral_const_mul]
  calc
    _ ≤ ∑ x, w x * ((q : ℝ) ^ (k + 1) *
        cavityGaussianAbsMoment (2 * (k + 1)) * L ^ (k + 1)) :=
      Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left
        (cavity_frame_even_moment_bound_of_norm hn μ (v x) u hu k L (hv x)) (hw x))
    _ = _ := by rw [← Finset.sum_mul, hsum, one_mul]

end InvariantIsing

end

end OAI
