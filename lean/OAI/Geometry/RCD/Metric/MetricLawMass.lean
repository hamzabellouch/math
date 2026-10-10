import OAI.Geometry.RCD.Metric.MeasuredBallSetIntegrals

namespace OAI

/-! # Exact masses and lower bounds for the actual approximation laws -/

open Set Metric MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [BorelSpace X] in
theorem normalizedBallPushforward_real {n : ℕ} (μ : Measure X) (p : X) (r S : ℝ)
    (V : X → Euclidean n) (hfin : μ (ball p (S*r)) ≠ ⊤)
    (hpos : 0 < μ.real (ball p (S*r))) (hVm : Measurable V)
    {A : Set (Euclidean n)} (hA : MeasurableSet A) :
    (normalizedBallPushforward μ p r S V hfin : Measure (Euclidean n)).real A =
      (μ.real (ball p (S*r)))⁻¹*μ.real (V ⁻¹' A ∩ ball p (S*r)) := by
  simpa only [setIntegral_const,smul_eq_mul,mul_one] using
    normalizedBallPushforward_setIntegral μ p r S V hfin hpos hVm hA
      (measurable_const : Measurable (fun _ : Euclidean n => (1:ℝ)))

omit [BorelSpace X] in
theorem normalizedBallPushforward_mass_lower {n : ℕ} (μ : Measure X)
    (p : X) (r S : ℝ) (V : X → Euclidean n)
    (hfin : μ (ball p (S*r)) ≠ ⊤) (hpos : 0 < μ.real (ball p (S*r)))
    (hVm : Measurable V) {A : Set (Euclidean n)} (hA : MeasurableSet A)
    {B : Set X} (hsub : B ⊆ V ⁻¹' A ∩ ball p (S*r)) {D : ℝ} (hD : 0 < D)
    (hvol : μ.real (ball p (S*r)) ≤ D*μ.real B) :
    D⁻¹ ≤ (normalizedBallPushforward μ p r S V hfin : Measure (Euclidean n)).real A := by
  rw [normalizedBallPushforward_real μ p r S V hfin hpos hVm hA]
  have hbound : μ.real B ≤ μ.real (V ⁻¹' A ∩ ball p (S*r)) :=
    measureReal_mono hsub (ne_of_lt ((measure_mono inter_subset_right).trans_lt
      (lt_top_iff_ne_top.mpr hfin)))
  have hv : D⁻¹*μ.real (ball p (S*r)) ≤ μ.real B := by
    rw [← div_eq_inv_mul]
    exact (div_le_iff₀ hD).mpr (by simpa only [mul_comm] using hvol)
  calc
    D⁻¹ = (μ.real (ball p (S*r)))⁻¹*(D⁻¹*μ.real (ball p (S*r))) := by
      field_simp [hpos.ne']
    _ ≤ (μ.real (ball p (S*r)))⁻¹*μ.real B :=
      mul_le_mul_of_nonneg_left hv (inv_nonneg.mpr hpos.le)
    _ ≤ _ := mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hpos.le)

omit [MeasurableSpace X] [BorelSpace X] in
theorem pointed_source_ball_image {n : ℕ} {p q : X} {r S ε t : ℝ}
    (hr : 0 < r) {V : X → Euclidean n}
    (hV : IsPointedApproximation p 0 r S ε V)
    (hq : dist q p ≤ S*r) (hsub : ball q (t*r) ⊆ ball p (S*r))
    {z : Euclidean n} (hz : dist (V q) z ≤ ε) :
    ball q (t*r) ⊆ V ⁻¹' closedBall z (t+2*ε) ∩ ball p (S*r) := by
  intro x hx
  refine ⟨?_,hsub hx⟩
  have hd := (abs_le.mp (hV.2.1 x q (hsub hx).le hq)).2
  have ht : dist x q/r < t := (div_lt_iff₀ hr).mpr hx
  have hh := dist_triangle (V x) (V q) z
  change dist (V x) z ≤ t+2*ε
  linarith

end RegularPointCoordinates

end

end OAI
