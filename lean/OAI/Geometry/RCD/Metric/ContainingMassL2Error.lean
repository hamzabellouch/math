import OAI.Geometry.RCD.Heat.HeatOffDiagonalL2

namespace OAI

/-! # L2 errors normalized by the mass of a containing region -/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X]

theorem l2_product_error_of_containing_mass (μ : ℕ → Measure X)
    [∀ k, IsFiniteMeasure (μ k)] (m : ℕ → ℝ) (hmass : ∀ k, 0 < m k)
    (hmass_le : ∀ k, (μ k).real univ ≤ m k)
    (z b : ℕ → X → ℝ) (hz : ∀ k, MemLp (z k) 2 (μ k))
    (hbmeas : ∀ k, AEStronglyMeasurable (b k) (μ k)) {C : ℝ}
    (hb : ∀ᶠ k in atTop, ∀ᵐ x ∂μ k, |b k x|≤C)
    (hlim : Tendsto (fun k => (m k)⁻¹*∫ x, (z k x)^2 ∂μ k) atTop (𝓝 0)) :
    Tendsto (fun k => (m k)⁻¹*∫ x, z k x*b k x ∂μ k) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  have hd : 0<δ^2/(C^2+1) := div_pos (sq_pos_of_pos hδ) (by positivity)
  filter_upwards [hb,hlim.eventually (Iio_mem_nhds hd)] with k hbk hzk
  have hbm : MemLp (b k) 2 (μ k) := MemLp.of_bound (hbmeas k) C
    (hbk.mono fun x hx => by simpa only [Real.norm_eq_abs] using hx)
  have hbsq : (∫ x, (b k x)^2 ∂μ k)≤C^2*m k := by
    have hh := integral_mono_ae hbm.integrable_sq (integrable_const (C^2))
      (hbk.mono fun x hx => by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hx 2)
    have hh' : (∫ x, (b k x)^2 ∂μ k)≤C^2*(μ k).real univ := by
      simpa only [integral_const,smul_eq_mul,mul_comm] using hh
    exact hh'.trans (mul_le_mul_of_nonneg_left (hmass_le k) (sq_nonneg C))
  have hcs := integral_mul_sq_le_integral_sq (μ k) (z k) (b k) (hz k) hbm
  have hs : |(m k)⁻¹*∫ x, z k x*b k x ∂μ k|^2≤
      ((m k)⁻¹*∫ x, (z k x)^2 ∂μ k)*C^2 := by
    calc
      _ = (m k)⁻¹^2*|∫ x, z k x*b k x ∂μ k|^2 := by rw [abs_mul,mul_pow,sq_abs]
      _ ≤ (m k)⁻¹^2*((∫ x, (z k x)^2 ∂μ k)*(∫ x, (b k x)^2 ∂μ k)) :=
        mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
      _ ≤ (m k)⁻¹^2*((∫ x, (z k x)^2 ∂μ k)*(C^2*m k)) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        exact mul_le_mul_of_nonneg_left hbsq (integral_nonneg fun _ => sq_nonneg _)
      _ = _ := by field_simp [(hmass k).ne']
  have hsmall : ((m k)⁻¹*∫ x, (z k x)^2 ∂μ k)*C^2<δ^2 := by
    have hzn : 0≤(m k)⁻¹*∫ x, (z k x)^2 ∂μ k :=
      mul_nonneg (inv_nonneg.mpr (hmass k).le) (integral_nonneg fun _ => sq_nonneg _)
    have hh := (lt_div_iff₀ (show 0<C^2+1 by positivity)).mp hzk
    nlinarith
  rw [Real.dist_eq,sub_zero]
  exact (sq_lt_sq₀ (abs_nonneg _) hδ.le).mp (hs.trans_lt hsmall)

end RegularPointCoordinates

end

end OAI
