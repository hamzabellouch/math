import OAI.Geometry.RCD.Metric.BallAverageBad
import OAI.Geometry.RCD.Sobolev.CompactBadAverage

namespace OAI

/-! # Local weak L1 control from the finite ball covering -/

open Set Metric MeasureTheory Filter
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem local_weak_maximal (μ : Measure X) [μ.InnerRegularCompactLTTop]
    {f : X → ℝ} (hf : Integrable f μ) (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x)
    (hfin : ∀ x r, μ (ball x r) ≠ ⊤) (p : X)
    {R D t : ℝ} (hD : 0 ≤ D) (ht : 0 < t)
    (hdoub : ∀ x r, 0 < r → r ≤ R → μ.real (ball x (5*r)) ≤ D*μ.real (ball x r)) :
    μ.real (ball p R ∩ ballAverageBad μ f R t) ≤ (D/t)*∫ y, f y ∂μ := by
  let A := ball p R ∩ ballAverageBad μ f R t
  have hAm : MeasurableSet A := measurableSet_ball.inter
    (isOpen_ballAverageBad μ hf hf0 hfin ht.le).measurableSet
  have hAfin : μ A ≠ ⊤ := measure_ne_top_of_subset inter_subset_left (hfin p R)
  let b := (D/t)*∫ y, f y ∂μ
  have hb : 0 ≤ b := mul_nonneg (div_nonneg hD ht.le) (integral_nonneg_of_ae hf0)
  change μ.real A ≤ b
  by_contra hnot
  have hlt : ENNReal.ofReal b < μ A :=
    (ENNReal.ofReal_lt_iff_lt_toReal hb hAfin).mpr (lt_of_not_ge hnot)
  obtain ⟨H,hHA,hH,hHm⟩ := hAm.exists_lt_isCompact_of_ne_top hAfin hlt
  have hHfin : μ H ≠ ⊤ := measure_ne_top_of_subset hHA hAfin
  have hHb : b < μ.real H := (ENNReal.ofReal_lt_iff_lt_toReal hb hHfin).mp hHm
  have hbound : t*μ.real H ≤ D*∫ y, f y ∂μ := by
    have hh := compact_bad_average μ hH (Ω := Set.univ) hf.integrableOn
      (by simpa using hf0) hfin hD ht.le hdoub ?_
    · simpa only [setIntegral_univ] using hh
    · intro x hx
      obtain ⟨r,hr,hrR,havg⟩ := (hHA hx).2
      exact ⟨r,hr,hrR.le,subset_univ _,havg.le⟩
  have hle : μ.real H ≤ b := by
    change μ.real H ≤ (D/t)*(∫ y, f y ∂μ)
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ ht).mpr
    simpa only [mul_comm] using hbound
  exact (not_lt_of_ge hle) hHb

end RegularPointCoordinates

end

end OAI
