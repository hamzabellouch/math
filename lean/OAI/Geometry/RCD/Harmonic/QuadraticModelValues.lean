import OAI.Geometry.RCD.Harmonic.MetricQuadraticError
import OAI.Geometry.RCD.Coordinates.BoundedLocalCoordinates
import OAI.Geometry.RCD.Harmonic.HarmonicQuadraticPotential

namespace OAI

/-! # Values and local metric accuracy of the actual quadratic model -/

open Set Metric MeasureTheory
open scoped NNReal BigOperators

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

theorem coordinateQuadratic_bound {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (C : ℝ≥0) (hu : ∀ j, ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ (u j) x| ≤ C) :
    ∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ (coordinateQuadratic μ hQ u C) x ∧
      |SobolevSpace.toLp μ hQ (coordinateQuadratic μ hQ u C) x| ≤ (n : ℝ) * (C : ℝ) ^ 2 / 2 := by
  have hb := (Filter.eventually_all_finset (Finset.univ : Finset (Fin n))).mpr (fun j _ => hu j)
  filter_upwards [coordinateQuadratic_representative μ hQ u C hu, hb] with x hx hbound
  rw [hx]
  have hnonneg : 0 ≤ ∑ j, (1 / 2 : ℝ) * (SobolevSpace.toLp μ hQ (u j) x) ^ 2 :=
    Finset.sum_nonneg fun j _ => mul_nonneg (by norm_num) (sq_nonneg _)
  refine ⟨hnonneg, ?_⟩
  rw [abs_of_nonneg hnonneg]
  calc
    _ ≤ ∑ _j : Fin n, (1 / 2 : ℝ) * (C : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) C.coe_nonneg).mpr (hbound j hj)
    _ = _ := by simp; ring

/-- The finite-coordinate definition agrees with the squared Euclidean norm
on every region where the columns represent that coordinate map. -/
theorem coordinateQuadratic_eq_norm {n : ℕ} {Ω : Set X}
    (u : Fin n → SobolevSpace μ hQ) (C : ℝ≥0) (v : X → Euclidean n)
    (hu : ∀ j, ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ (u j) x| ≤ C)
    (hrep : ∀ j, SobolevSpace.toLp μ hQ (u j) =ᵐ[μ.restrict Ω] fun x => v x j) :
    SobolevSpace.toLp μ hQ (coordinateQuadratic μ hQ u C) =ᵐ[μ.restrict Ω]
      fun x => ‖v x‖ ^ 2 / 2 := by
  have hr := (Filter.eventually_all_finset (Finset.univ : Finset (Fin n))).mpr (fun j _ => hrep j)
  filter_upwards [ae_restrict_of_ae (coordinateQuadratic_representative μ hQ u C hu), hr]
    with x hx hrx
  rw [hx, EuclideanSpace.real_norm_sq_eq]
  simp only [hrx _ (Finset.mem_univ _), ← Finset.mul_sum]
  ring

variable [BorelSpace X] [ProperSpace X]

/-- The actual clipped extensions are harmonic, globally bounded and
pointwise unchanged on the metric-approximation region. -/
theorem bounded_metric_coordinates {n : ℕ} {p : X} {r R ε : ℝ}
    (hr : 0 < r) (hR : 0 ≤ R) (hε : 0 ≤ ε)
    (u : Fin n → SobolevSpace μ hQ) (v : X → Euclidean n)
    (hu : ∀ j, IsSobolevHarmonicOn μ hQ (ball p (R * r)) (u j))
    (hrep : ∀ j, SobolevSpace.toLp μ hQ (u j) =ᵐ[μ.restrict (ball p (R * r))] fun x => v x j)
    (hv : v p = 0)
    (hmetric : IsPointedApproximation p 0 r R ε (fun x => r⁻¹ • v x)) :
    let C : ℝ≥0 := ⟨r * (R + ε), mul_nonneg hr.le (add_nonneg hR hε)⟩
    let w := fun j => boundedLocalVersion μ hQ (u j) C
    (∀ j, ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ (w j) x| ≤ C) ∧
    (∀ j, IsSobolevHarmonicOn μ hQ (ball p (R * r)) (w j)) ∧
    (∀ j, SobolevSpace.toLp μ hQ (w j) =ᵐ[μ.restrict (ball p (R * r))] fun x => v x j) := by
  dsimp only
  let C : ℝ≥0 := ⟨r * (R + ε), mul_nonneg hr.le (add_nonneg hR hε)⟩
  have hb (j : Fin n) : ∀ᵐ x ∂μ.restrict (ball p (R * r)), |SobolevSpace.toLp μ hQ (u j) x| ≤ C := by
    filter_upwards [hrep j, ae_restrict_mem measurableSet_ball] with x hx hxb
    rw [hx]
    have hnorm := (hmetric.centered_norm_error hr hR (by rw [hv, smul_zero]) hxb.le).2
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le)] at hnorm
    have hnorm' : ‖v x‖ ≤ r * (R + ε) := by
      have ht := mul_le_mul_of_nonneg_left hnorm hr.le
      simpa only [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul] using ht
    have hi : |v x j| ≤ ‖v x‖ := by
      simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le (v x) j)
    exact hi.trans hnorm'
  refine ⟨fun j => boundedLocalVersion_bound μ hQ (u j) C,
    fun j => boundedLocalVersion_harmonic μ hQ measurableSet_ball (u j) C (hb j) (hu j), ?_⟩
  intro j
  exact (boundedLocalVersion_eq μ hQ (u j) C (hb j)).trans (hrep j)

omit [ProperSpace X] in
/-- A metric approximation supplies precisely the value-error premise in
the cutoff gradient comparison, using the actual coordinate quadratic. -/
theorem coordinateQuadratic_metric_value_error {n : ℕ} {p : X} {r R ε : ℝ}
    (hr : 0 < r) (hR : 0 ≤ R) (hε : 0 ≤ ε)
    (u : Fin n → SobolevSpace μ hQ) (C : ℝ≥0) (v : X → Euclidean n)
    (hu : ∀ j, ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ (u j) x| ≤ C)
    (hrep : ∀ j, SobolevSpace.toLp μ hQ (u j) =ᵐ[μ.restrict (ball p (R * r))] fun x => v x j)
    (hv : v p = 0)
    (hmetric : IsPointedApproximation p 0 r R ε (fun x => r⁻¹ • v x))
    (q : SobolevSpace μ hQ)
    (hq : SobolevSpace.toLp μ hQ q =ᵐ[μ.restrict (ball p (R * r))]
      fun x => dist p x ^ 2 / 2) :
    ∀ᵐ x ∂μ.restrict (ball p (R * r)),
      |SobolevSpace.toLp μ hQ (q - coordinateQuadratic μ hQ u C) x| ≤
        r ^ 2 * (ε * (2 * R + ε) / 2) := by
  filter_upwards [hq, coordinateQuadratic_eq_norm μ hQ u C v hu hrep,
    ae_restrict_of_ae (Lp.coeFn_sub (SobolevSpace.toLp μ hQ q)
      (SobolevSpace.toLp μ hQ (coordinateQuadratic μ hQ u C))),
    ae_restrict_mem measurableSet_ball] with x hqx hHx hsub hx
  change |(SobolevSpace.toLp μ hQ q - SobolevSpace.toLp μ hQ (coordinateQuadratic μ hQ u C)) x| ≤ _
  rw [hsub, Pi.sub_apply, hqx, hHx]
  have hmetricx := hmetric.quadratic_value_error hr hR hε (by rw [hv, smul_zero]) hx.le
  have hnorm : r ^ 2 * ‖r⁻¹ • v x‖ ^ 2 = ‖v x‖ ^ 2 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
    field_simp
  rwa [hnorm] at hmetricx

end RegularPointCoordinates

end

end OAI
