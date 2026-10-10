import OAI.MeasureTheory.Falconer.Estimates.ScaledWeightedInverse
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

namespace OAI

/-! # The inverse remainder under the original pair measure

The scaled distance weight and the original endpoint laws are retained.
The estimate integrates the pointwise stationary remainder; no change of
measure or unproved Fourier estimate is used.
-/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ContDiff

noncomputable def scaledDistanceKernel (m : ℕ) (s r : ℝ)
    (B : Space (m+3) → Space (m+3) → Space (m+3) → ℂ)
    (z : Space (m+3) × Space (m+3)) : ℂ :=
  (((dist z.1 z.2/s)^(-(((m+2 : ℕ) : ℝ)/2)) : ℝ) : ℂ)*
    Complex.exp (Complex.I*((r*dist z.1 z.2 : ℝ) : ℂ))*B z.1 z.2 (NormedSpace.normalize (z.1-z.2))

theorem scaledDistanceKernel_measurable (m : ℕ) (s r : ℝ)
    (B : Space (m+3) → Space (m+3) → Space (m+3) → ℂ)
    (hB : Measurable (fun p : (Space (m+3) × Space (m+3)) × Space (m+3) =>
      B p.1.1 p.1.2 p.2)) : Measurable (scaledDistanceKernel m s r B) := by
  have hn : Measurable (fun z : Space (m+3) × Space (m+3) => NormedSpace.normalize (z.1-z.2)) := by
    unfold NormedSpace.normalize
    fun_prop
  unfold scaledDistanceKernel
  apply Measurable.mul
  · fun_prop
  · exact hB.comp (measurable_id.prodMk hn)

theorem scaledDistanceKernel_integrable (m : ℕ) (s r δ : ℝ) (hδ : 0 < δ)
    (μ ν : Measure (Space (m+3))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hsep : ∀ᵐ z ∂μ.prod ν, δ ≤ dist z.1 z.2/s)
    (B : Space (m+3) → Space (m+3) → Space (m+3) → ℂ)
    (hB : Measurable (fun p : (Space (m+3) × Space (m+3)) × Space (m+3) =>
      B p.1.1 p.1.2 p.2))
    {C : ℝ} (hbound : ∀ x y w, ‖B x y w‖ ≤ C) :
    Integrable (scaledDistanceKernel m s r B) (μ.prod ν) := by
  apply Integrable.of_bound (scaledDistanceKernel_measurable m s r B hB).aestronglyMeasurable
    (δ^(-(((m+2 : ℕ) : ℝ)/2))*C)
  filter_upwards [hsep] with z hz
  have hp : 0 ≤ (dist z.1 z.2/s)^(-(((m+2 : ℕ) : ℝ)/2)) :=
    Real.rpow_nonneg (hδ.trans_le hz).le _
  have he : ‖Complex.exp (Complex.I*((r*dist z.1 z.2 : ℝ) : ℂ))‖ = 1 := by
    simp [Complex.norm_exp,Complex.mul_re,Complex.mul_im]
  simp only [scaledDistanceKernel,norm_mul,he,mul_one,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg hp]
  exact mul_le_mul
    (Real.rpow_le_rpow_of_nonpos hδ hz (neg_nonpos.mpr (by positivity)))
    (hbound _ _ _) (norm_nonneg _) (Real.rpow_nonneg hδ.le _)

theorem exists_integrated_scaled_inverse_order
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m : ℕ) {κ T : ℝ} (hκ : 0 < κ) :
    ∃ J : ℕ, ∃ A : ℝ, 0 ≤ A ∧
      ∀ R D s r δ : ℝ, 1 ≤ R → 1 ≤ D → D ≤ R^2 → 0 < s → 0 < δ →
      ∀ (μ ν : Measure (Space (m+3))) [IsFiniteMeasure μ] [IsFiniteMeasure ν],
      (∀ᵐ z ∂μ.prod ν, δ ≤ dist z.1 z.2/s) →
      (∀ᵐ z : Space (m+3) × Space (m+3) ∂μ.prod ν,
        ‖NormedSpace.normalize (z.1-z.2)-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/8) →
      (∀ᵐ z ∂μ.prod ν, 1 ≤ r*dist z.1 z.2 ∧ D^2/(r*dist z.1 z.2) ≤ R^(-κ)) →
      ∀ B : Space (m+3) → Space (m+3) → Space (m+3) → ℂ,
      Measurable (fun p : (Space (m+3) × Space (m+3)) × Space (m+3) => B p.1.1 p.1.2 p.2) →
      (∀ x y, ContDiff ℝ ∞ (B x y)) →
      ∀ C : ℝ, 0 ≤ C → (∀ x y w, ‖B x y w‖ ≤ C) →
      (∀ x y k, k ≤ 2*(J+1)+(m+2)+1 → ∀ w : Sphere (m+3),
        ‖iteratedFDeriv ℝ k (B x y) w‖ ≤ C*D^k) →
      Integrable (fun z : Space (m+3) × Space (m+3) =>
        scaledWeightedInverseSum m J s r (z.1-z.2) (B z.1 z.2)) (μ.prod ν) →
      ∀ M P : ℝ,
      ‖(M⁻¹*P⁻¹) • (∫ z : Space (m+3) × Space (m+3),
          scaledWeightedInverseSum m J s r (z.1-z.2) (B z.1 z.2) ∂μ.prod ν) -
        (M⁻¹*P⁻¹) • (∫ z, scaledDistanceKernel m s r B z ∂μ.prod ν)‖ ≤
      |M⁻¹*P⁻¹| *((δ^(-(((m+2 : ℕ) : ℝ)/2))*A*C*R^(-T))*(μ.prod ν).real univ) := by
  obtain ⟨J,A,hA,hi⟩ := exists_scaled_weighted_inverse_order hgnomonic hquadratic m (T := T) hκ
  refine ⟨J,A,hA,?_⟩
  intro R D s r δ hR hD hDR hs hδ μ ν _ _ hsep hnear hfreq B hBm hBs C hC hbound hderiv hInt M P
  have ht := scaledDistanceKernel_integrable m s r δ hδ μ ν hsep B hBm hbound
  have he : ∀ᵐ z ∂μ.prod ν,
      ‖scaledWeightedInverseSum m J s r (z.1-z.2) (B z.1 z.2) -
        scaledDistanceKernel m s r B z‖ ≤ δ^(-(((m+2 : ℕ) : ℝ)/2))*A*C*R^(-T) := by
    filter_upwards [hsep,hnear,hfreq] with z hz hn hf
    have hdist : 0 < dist z.1 z.2 := (div_pos_iff_of_pos_right hs).mp (hδ.trans_le hz)
    have hzne : z.1-z.2 ≠ 0 := by
      intro h
      exact (ne_of_gt hdist) (by rw [sub_eq_zero.mp h,dist_self])
    have hnorm : ‖z.1-z.2‖ = dist z.1 z.2 := rfl
    have hh := hi R D hR hD hDR (z.1-z.2) hzne hn (B z.1 z.2) (hBs _ _)
      C hC (hderiv _ _) s r hs (by simpa only [hnorm] using hf.1)
      (by simpa only [hnorm] using hf.2)
    simp only [hnorm] at hh
    change ‖scaledWeightedInverseSum m J s r (z.1-z.2) (B z.1 z.2) -
      scaledDistanceKernel m s r B z‖ ≤ _ at hh
    apply hh.trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_nonpos hδ hz (neg_nonpos.mpr (by positivity))) hA) hC)
      (Real.rpow_nonneg (zero_le_one.trans hR) _)
  rw [← smul_sub,← integral_sub hInt ht,norm_smul,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (norm_integral_le_of_norm_le_const he) (abs_nonneg _)

end Falconer

end OAI
