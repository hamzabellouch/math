import OAI.Probability.InvariantIsing.Cavity.CavityProjectedSpinNumerator
import OAI.Probability.InvariantIsing.Cavity.CavityFrameMoments

namespace OAI

/-! Uniform ordinary fourth moments for the actual selected Haar axes.
These are the physical-side moments used to remove the normalizer floor. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators RealInnerProductSpace

namespace InvariantIsing

lemma cavity_sphere_fourth_moment_of_norm {n : ℕ} (hn : 0 < n)
    (μ : Measure (Orthogonal n)) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (v u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1)
    {C : ℝ} (hv : ‖v‖^2 ≤ C * n) :
    (∫ U, |⟪v, matrixRotation U u⟫|^4 ∂μ) ≤ cavityGaussianAbsMoment 4 * C^2 := by
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hr : ‖v‖^2 / (n : ℝ) ≤ C := (div_le_iff₀ hn').mpr hv
  have h := cavity_sphere_even_moment_bound hn μ v u hu 2
  norm_num only [Nat.reduceMul] at h
  calc
    _ ≤ cavityGaussianAbsMoment 4 * ‖v‖^4 / (n : ℝ)^2 := h
    _ = cavityGaussianAbsMoment 4 * (‖v‖^2 / (n : ℝ))^2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (div_nonneg (sq_nonneg _) hn'.le) hr 2)
      (cavityGaussianAbsMoment_nonneg 4)

lemma cavity_selected_site_inner {m q d : ℕ} {N : Fin m → ℕ}
    (e : Fin d → Fin m × Fin q) (v : (a : Fin m) → Fin (N a) → ℝ)
    (A₀ : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ)
    (U : (a : Fin m) → Orthogonal (N a)) (j : Fin d) :
    cavitySelectedSiteProjection e (fun a (_ : Unit) => v a) (cavityGroupHaarFrames A₀ U) () j =
      ⟪(WithLp.toLp 2 (v (e j).1) : EuclideanSpace ℝ (Fin (N (e j).1))),
        matrixRotation (U (e j).1) (WithLp.toLp 2 (fun l => A₀ (e j).1 l (e j).2))⟫ := by
  simp only [cavitySelectedSiteProjection, PiLp.toLp_apply, cavityGroupHaarFrames,
    Matrix.mul_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial,
    matrixRotation_apply]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

lemma continuous_cavitySelectedSiteProjection {m q d : ℕ} {N : Fin m → ℕ}
    (e : Fin d → Fin m × Fin q) (v : (a : Fin m) → Fin (N a) → ℝ)
    (A₀ : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ) :
    Continuous (fun U : (a : Fin m) → Orthogonal (N a) =>
      cavitySelectedSiteProjection e (fun a (_ : Unit) => v a) (cavityGroupHaarFrames A₀ U) ()) := by
  unfold cavitySelectedSiteProjection cavityGroupHaarFrames
  fun_prop

theorem cavity_selected_haar_fourth_moment {m q d : ℕ} {N : Fin m → ℕ}
    (hN : ∀ a, 0 < N a)
    (μ : (a : Fin m) → Measure (Orthogonal (N a)))
    [∀ a, IsProbabilityMeasure (μ a)] [∀ a, (μ a).IsMulRightInvariant]
    (e : Fin d → Fin m × Fin q) (v : (a : Fin m) → Fin (N a) → ℝ)
    (A₀ : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ)
    (hA₀ : ∀ a, (A₀ a).transpose * A₀ a = 1) {C : ℝ}
    (hv : ∀ a, ‖(WithLp.toLp 2 (v a) : EuclideanSpace ℝ (Fin (N a)))‖^2 ≤ C * N a) :
    (∫ U, ‖cavitySelectedSiteProjection e (fun a (_ : Unit) => v a)
      (cavityGroupHaarFrames A₀ U) ()‖^4 ∂Measure.pi μ) ≤
      (d : ℝ)^2 * cavityGaussianAbsMoment 4 * C^2 := by
  let Y := fun U : (a : Fin m) → Orthogonal (N a) =>
    cavitySelectedSiteProjection e (fun a (_ : Unit) => v a) (cavityGroupHaarFrames A₀ U) ()
  have hu (j : Fin d) : ‖(WithLp.toLp 2 (fun l => A₀ (e j).1 l (e j).2) :
      EuclideanSpace ℝ (Fin (N (e j).1)))‖ = 1 :=
    (cavity_orthonormal_of_gram (A₀ (e j).1) (hA₀ (e j).1)).norm_eq_one (e j).2
  have hcoord (U) (j : Fin d) : |Y U j| ≤ ‖(WithLp.toLp 2 (v (e j).1) :
      EuclideanSpace ℝ (Fin (N (e j).1)))‖ := by
    dsimp only [Y]
    rw [cavity_selected_site_inner]
    simpa only [(matrixRotation _).norm_map, hu j, mul_one] using
      abs_real_inner_le_norm (WithLp.toLp 2 (v (e j).1))
        (matrixRotation (U (e j).1) (WithLp.toLp 2 (fun l => A₀ (e j).1 l (e j).2)))
  have hm (j : Fin d) : Measurable (fun U : Orthogonal (N (e j).1) =>
      |⟪(WithLp.toLp 2 (v (e j).1) : EuclideanSpace ℝ (Fin (N (e j).1))),
        matrixRotation U (WithLp.toLp 2 (fun l => A₀ (e j).1 l (e j).2))⟫|^4) := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial,
      matrixRotation_apply]
    apply Measurable.pow_const
    apply Measurable.abs
    apply Finset.measurable_sum
    intro i _
    apply Measurable.mul_const
    apply Finset.measurable_sum
    intro l _
    exact (((measurable_pi_apply l).comp ((measurable_pi_apply i).comp
      measurable_subtype_coe)).mul_const _)
  have hcm (j : Fin d) : Measurable (fun U => |Y U j|^4) := by
    simpa only [Y, cavity_selected_site_inner, Function.comp_def] using
      (hm j).comp (measurable_pi_apply (e j).1)
  have hci (j : Fin d) : Integrable (fun U => |Y U j|^4) (Measure.pi μ) := by
    apply Integrable.of_bound (hcm j).aestronglyMeasurable
      (‖(WithLp.toLp 2 (v (e j).1) : EuclideanSpace ℝ (Fin (N (e j).1)))‖^4)
    apply ae_of_all
    intro U
    change ‖|Y U j|^4‖ ≤ _
    simpa only [Real.norm_eq_abs, abs_pow, abs_abs] using
      pow_le_pow_left₀ (abs_nonneg _) (hcoord U j) 4
  have hb (j : Fin d) : (∫ U, |Y U j|^4 ∂Measure.pi μ) ≤ cavityGaussianAbsMoment 4 * C^2 := by
    have h := cavity_sphere_fourth_moment_of_norm (hN (e j).1) (μ (e j).1)
      (WithLp.toLp 2 (v (e j).1)) (WithLp.toLp 2 (fun l => A₀ (e j).1 l (e j).2)) (hu j) (hv (e j).1)
    have he := (measurePreserving_eval μ (e j).1).hasLaw.integral_comp (hm j).aestronglyMeasurable
    simpa only [Y, cavity_selected_site_inner, Function.comp_def, Function.eval] using he.le.trans h
  have hpoint (U) : ‖Y U‖^4 ≤ (d : ℝ) * ∑ j, |Y U j|^4 := by
    have h := pow_sum_le_card_mul_sum_pow (s := Finset.univ)
      (f := fun j : Fin d => (Y U j)^2) (fun _ _ => sq_nonneg _) 1
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, EuclideanSpace.real_norm_sq_eq]
    simpa only [Nat.reduceAdd, pow_one, Finset.card_univ, Fintype.card_fin, pow_mul,
      sq_abs] using h
  calc
    _ ≤ ∫ U, (d : ℝ) * ∑ j, |Y U j|^4 ∂Measure.pi μ :=
      integral_mono_of_nonneg (ae_of_all _ (fun U => pow_nonneg (norm_nonneg _) _))
        ((integrable_finsetSum _ fun j _ => hci j).const_mul d) (ae_of_all _ hpoint)
    _ = (d : ℝ) * ∑ j, ∫ U, |Y U j|^4 ∂Measure.pi μ := by
      rw [integral_const_mul, integral_finsetSum _ fun j _ => hci j]
    _ ≤ (d : ℝ) * ∑ _j : Fin d, cavityGaussianAbsMoment 4 * C^2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hb j) (Nat.cast_nonneg d)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end InvariantIsing

end

end OAI
