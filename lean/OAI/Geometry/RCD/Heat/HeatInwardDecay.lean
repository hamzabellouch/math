import OAI.Geometry.RCD.Heat.HeatOffDiagonalL2

namespace OAI

/-! # Inward L² heat decay by self-adjointness -/

open Set Filter MeasureTheory Metric
open scoped NNReal ENNReal Topology InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)

theorem heatAt_inward_L2_tail (f : Lp ℝ 2 μ) (p : X) {r R t : ℝ}
    (hf : ∀ᵐ x ∂μ, f x ≠ 0 → R ≤ dist p x) (hrR : r ≤ R) (ht : 0 < t)
    {S : Set X} (hS : MeasurableSet S) (hnear : ∀ x ∈ S, dist p x ≤ r) :
    (∫ x in S, (heatAt μ hQ t f x)^2 ∂μ) ≤
      Real.exp (-(R-r)^2/(2*t))*‖f‖^2 := by
  let u := heatAt μ hQ t f
  have hv := (Lp.memLp u).indicator hS
  let v := hv.toLp (S.indicator u)
  have hve : v =ᵐ[μ] S.indicator u := hv.coeFn_toLp
  have hvnear : ∀ᵐ x ∂μ, v x ≠ 0 → dist p x ≤ r := by
    filter_upwards [hve] with x hx hn
    have hs : x ∈ S := by
      by_contra h
      simp only [hx,indicator_of_notMem h] at hn
      exact hn rfl
    exact hnear x hs
  have hsq : ‖v‖^2 = ∫ x in S, (u x)^2 ∂μ := by
    rw [← integral_sq_Lp μ v,← integral_indicator hS]
    apply integral_congr_ae
    filter_upwards [hve] with x hx
    rw [hx]
    by_cases hs : x ∈ S <;> simp only [indicator_of_mem,indicator_of_notMem,hs,zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true]
  have he : inner ℝ u v = ‖v‖^2 := by
    rw [hsq,L2.inner_def,← integral_indicator hS]
    apply integral_congr_ae
    filter_upwards [hve] with x hx
    rw [hx]
    by_cases hs : x ∈ S
    · simp only [indicator_of_mem hs,Real.inner_apply,pow_two]
    · simp only [indicator_of_notMem hs,Real.inner_apply,mul_zero]
  have hh := heatAt_radial_pairing μ hQ v f p hvnear hf hrR ht
  have he' : inner ℝ (heatAt μ hQ t v) f = ‖v‖^2 := by
    rw [heatAt_inner,real_inner_comm]
    exact he
  rw [he',abs_of_nonneg (sq_nonneg _)] at hh
  have hnorm : ‖v‖ ≤ Real.exp (-(R-r)^2/(4*t))*‖f‖ := by
    by_cases hvzero : ‖v‖ = 0
    · rw [hvzero]
      positivity
    have hvpos : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg v) (Ne.symm hvzero)
    apply (mul_le_mul_iff_left₀ hvpos).mp
    simpa only [pow_two,mul_assoc,mul_comm,mul_left_comm] using hh
  have hpower := pow_le_pow_left₀ (norm_nonneg v) hnorm 2
  have hexp : Real.exp (-(R-r)^2/(4*t))^2 = Real.exp (-(R-r)^2/(2*t)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
    ring
  rw [mul_pow,hexp,hsq] at hpower
  exact hpower

end RegularPointCoordinates

end

end OAI
