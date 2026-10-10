import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.MeasureBounds

namespace OAI

/-!
# Least-squared approximation by affine planes

The squared excess minimizes the radius-normalized quadratic distance over affine planes
of the prescribed dimension. Local finiteness ensures that these distance integrals exist
on balls.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology

def IsAffineNPlane {d : ℕ} (n : ℕ) (S : AffineSubspace ℝ (Ambient d)) : Prop :=
  (S : Set (Ambient d)).Nonempty ∧ Module.finrank ℝ S.direction = n

def quadraticPlaneError {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (r : ℝ) (S : AffineSubspace ℝ (Ambient d)) : ℝ :=
  (r ^ (n + 2))⁻¹ * ∫ x in ball a r, infDist x (S : Set (Ambient d)) ^ 2 ∂μ

def squaredExcess {d : ℕ} (n : ℕ) (μ : Measure (Ambient d)) (a : Ambient d) (r : ℝ) : ℝ :=
  sInf {t : ℝ | ∃ S : AffineSubspace ℝ (Ambient d),
    IsAffineNPlane n S ∧ t = quadraticPlaneError n μ a r S}

theorem squared_infDist_integrableOn_ball {d : ℕ} (μ : Measure (Ambient d))
    [IsFiniteMeasureOnCompacts μ] (a : Ambient d) (r : ℝ)
    (s : Set (Ambient d)) (hs : s.Nonempty) :
    IntegrableOn (fun x => infDist x s ^ 2) (ball a r) μ := by
  have : IsFiniteMeasure (μ.restrict (ball a r)) := isFiniteMeasure_restrict.mpr
    (ne_of_lt ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall a r).measure_lt_top))
  obtain ⟨p, hp⟩ := hs
  have hm : MemLp (fun x => infDist x s) 2 (μ.restrict (ball a r)) := by
    apply MemLp.of_bound (continuous_infDist_pt s).aestronglyMeasurable (r + dist a p)
    filter_upwards [ae_restrict_mem (μ := μ) measurableSet_ball] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg infDist_nonneg]
    have hx' : dist x a ≤ r := hx.le
    exact (infDist_le_dist_of_mem hp).trans ((dist_triangle x a p).trans
      (add_le_add hx' (le_refl (dist a p))))
  exact hm.integrable_sq

theorem quadraticPlaneError_nonneg {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (r : ℝ) (hr : 0 ≤ r) (S : AffineSubspace ℝ (Ambient d)) :
    0 ≤ quadraticPlaneError n μ a r S :=
  mul_nonneg (inv_nonneg.mpr (pow_nonneg hr _))
    (integral_nonneg fun x => sq_nonneg (infDist x (S : Set (Ambient d))))

theorem squaredExcess_nonneg {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (r : ℝ) (hr : 0 ≤ r) : 0 ≤ squaredExcess n μ a r := by
  apply Real.sInf_nonneg
  rintro t ⟨S, _hS, rfl⟩
  exact quadraticPlaneError_nonneg n μ a r hr S

theorem squaredExcess_le_planeError {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (r : ℝ) (hr : 0 ≤ r)
    (S : AffineSubspace ℝ (Ambient d)) (hS : IsAffineNPlane n S) :
    squaredExcess n μ a r ≤ quadraticPlaneError n μ a r S := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro t ⟨T, _hT, rfl⟩
    exact quadraticPlaneError_nonneg n μ a r hr T
  · exact ⟨S, hS, rfl⟩

theorem squaredExcess_div_sq_le {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (r : ℝ) (hr : 0 ≤ r)
    (S : AffineSubspace ℝ (Ambient d)) (hS : IsAffineNPlane n S) (δ : ℝ) :
    squaredExcess n μ a r / δ ^ 2 ≤ (r ^ (n + 2))⁻¹ *
      ∫ x in ball a r, (infDist x (S : Set (Ambient d)) / δ) ^ 2 ∂μ := by
  calc
    _ ≤ quadraticPlaneError n μ a r S / δ ^ 2 :=
      div_le_div_of_nonneg_right (squaredExcess_le_planeError n μ a r hr S hS) (sq_nonneg δ)
    _ = _ := by
      simp only [quadraticPlaneError, div_pow, integral_div]
      ring

theorem squaredExcess_ratio_tendsto_zero_of_planes {d : ℕ} (n : ℕ)
    (μ : ℕ → Measure (Ambient d)) (a : Ambient d) (r : ℝ) (hr : 0 ≤ r)
    (S : ℕ → AffineSubspace ℝ (Ambient d)) (hS : ∀ j, IsAffineNPlane n (S j))
    (δ : ℕ → ℝ)
    (hlim : Tendsto (fun j => ∫ x in ball a r,
      (infDist x (S j : Set (Ambient d)) / δ j) ^ 2 ∂μ j) atTop (𝓝 0)) :
    Tendsto (fun j => squaredExcess n (μ j) a r / δ j ^ 2) atTop (𝓝 0) := by
  have hlim' := hlim.const_mul ((r ^ (n + 2))⁻¹)
  simp only [mul_zero] at hlim'
  exact squeeze_zero (fun j => div_nonneg (squaredExcess_nonneg n (μ j) a r hr) (sq_nonneg _))
    (fun j => squaredExcess_div_sq_le n (μ j) a r hr (S j) (hS j) (δ j)) hlim'

end

end RieszRectifiability

end OAI
