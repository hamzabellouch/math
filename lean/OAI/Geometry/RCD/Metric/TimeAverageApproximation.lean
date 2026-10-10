import OAI.Geometry.RCD.Coordinates.TimeIntervalAverage

namespace OAI

/-! # Quantitative approximation by symmetric time averages -/

open Set Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates

theorem timeIntervalAverage_abs_sub_le (f : ℝ → ℝ) {h t A : ℝ} (hh : 0 < h)
    (hf : IntervalIntegrable f volume (t-h) (t+h))
    (hb : ∀ q ∈ Icc (t-h) (t+h), |f q-f t| ≤ A) :
    |timeIntervalAverage f h t-f t| ≤ A := by
  have h2 : 0 < 2*h := by positivity
  have hab : t-h ≤ t+h := by linarith
  have he : timeIntervalAverage f h t-f t =
      (2*h)⁻¹*(∫ q in (t-h)..(t+h), f q-f t) := by
    rw [intervalIntegral.integral_sub hf intervalIntegrable_const,
      intervalIntegral.integral_const]
    simp only [timeIntervalAverage,smul_eq_mul]
    field_simp
    ring
  have hi : |∫ q in (t-h)..(t+h), f q-f t| ≤ (2*h)*A := by
    calc
      _ ≤ ∫ q in (t-h)..(t+h), |f q-f t| :=
        intervalIntegral.abs_integral_le_integral_abs hab
      _ ≤ ∫ q in (t-h)..(t+h), A :=
        intervalIntegral.integral_mono_on hab (hf.sub intervalIntegrable_const).abs
          intervalIntegrable_const hb
      _ = _ := by rw [intervalIntegral.integral_const]; simp only [smul_eq_mul]; ring
  rw [he,abs_mul,abs_of_pos (inv_pos.mpr h2)]
  calc
    _ ≤ (2*h)⁻¹*((2*h)*A) := mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr h2.le)
    _ = A := by field_simp


theorem timeIntervalAverage_local_lipschitz_error
    {X : Type*} [MetricSpace X] (H : ℝ → X → ℝ)
    {Ω : Set X} {a b h t : ℝ} {L : ℝ≥0}
    (hH : LipschitzOnWith L (Function.uncurry H) (Ioo a b ×ˢ Ω))
    (hh : 0 < h) (ha : a < t-h) (hb : t+h < b) {x : X} (hx : x ∈ Ω) :
    |timeIntervalAverage (fun q => H q x) h t-H t x| ≤ L*h := by
  have hsub (q : ℝ) (hq : q ∈ Icc (t-h) (t+h)) : (q,x) ∈ Ioo a b ×ˢ Ω :=
    ⟨⟨ha.trans_le hq.1,hq.2.trans_lt hb⟩,hx⟩
  have ht : (t,x) ∈ Ioo a b ×ˢ Ω := ⟨⟨by linarith,by linarith⟩,hx⟩
  have hc : ContinuousOn (fun q => H q x) (Icc (t-h) (t+h)) :=
    hH.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn hsub
  apply timeIntervalAverage_abs_sub_le _ hh
    (hc.intervalIntegrable_of_Icc (by linarith))
  intro q hq
  have he := hH.dist_le_mul (q,x) (hsub q hq) (t,x) ht
  simp only [Function.uncurry,Prod.dist_eq,dist_self,Real.dist_eq,max_eq_left (abs_nonneg (q-t))] at he
  have habs : |q-t| ≤ h := abs_le.mpr ⟨by linarith [hq.1],by linarith [hq.2]⟩
  exact he.trans (mul_le_mul_of_nonneg_left habs L.coe_nonneg)

end RegularPointCoordinates

end

end OAI
