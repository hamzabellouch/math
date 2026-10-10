import OAI.Geometry.RCD.Metric.VanishingBallRatio
import OAI.Geometry.RCD.Sobolev.EuclideanEnergyRatios

namespace OAI

/-! # Exact power growth fixes the dimension of a local Euclidean realization -/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

theorem ball_ratio_tendsto_zero_outside_support {m : ℕ}
    (μ : Measure (Euclidean m)) [IsFiniteMeasure μ] {K : Set (Euclidean m)}
    (hK : IsClosed K) (hμ : ∀ᵐ x ∂μ, x ∈ K) {x : Euclidean m} (hx : x ∉ K) :
    Tendsto (fun r => μ.real (closedBall x r)/volume.real (closedBall x r))
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨R,hR,hball⟩ := Metric.isOpen_iff.mp hK.isOpen_compl x hx
  apply tendsto_const_nhds.congr'
  filter_upwards [Ioo_mem_nhdsGT hR] with r hr
  have hnull : μ (closedBall x r) = 0 := measure_mono_null
    ((closedBall_subset_ball hr.2).trans hball) (ae_iff.mp hμ)
  simp only [Measure.real,hnull,ENNReal.toReal_zero,zero_div]

theorem euclidean_dimension_of_power_ball_mass {m n : ℕ}
    (μ : Measure (Euclidean m)) [IsFiniteMeasure μ] {K : Set (Euclidean m)}
    (hK : IsClosed K) (hμ : ∀ᵐ x ∂μ, x ∈ K) (hmn : m ≤ n)
    {a S : ℝ} (ha : 0 < a) (hS : 0 < S)
    (hpos : 0 < μ.real (closedBall (0:Euclidean m) a))
    (hmass : ∀ x ∈ K ∩ closedBall (0:Euclidean m) a,
      ∀ r : ℝ, 0 < r → r ≤ a → μ.real (closedBall x r) = (r/S)^n) : m = n := by
  by_contra hne
  have hmn' : m < n := lt_of_le_of_ne hmn hne
  let d := n-m
  have hd : d ≠ 0 := by dsimp only [d]; omega
  have hn : n = m+d := by dsimp only [d]; omega
  have hratio : ∀ x ∈ closedBall (0:Euclidean m) a,
      Tendsto (fun r => μ.real (closedBall x r)/volume.real (closedBall x r))
        (𝓝[>] 0) (𝓝 0) := by
    intro x hx
    by_cases hxK : x ∈ K
    · have hv : 0 < volume.real (ball (0:Euclidean m) 1) :=
        ENNReal.toReal_pos (measure_ball_pos volume _ zero_lt_one).ne' measure_ball_ne_top
      have hid : Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝 0) :=
        tendsto_id.mono_right nhdsWithin_le_nhds
      have ht := (hid.pow d).div_const (S^n*volume.real (ball (0:Euclidean m) 1))
      simp only [zero_pow hd,zero_div] at ht
      apply ht.congr'
      filter_upwards [Ioc_mem_nhdsGT ha] with r hr
      rw [hmass x ⟨hxK,hx⟩ r hr.1 hr.2,
        Measure.addHaar_real_closedBall volume x hr.1.le,finrank_euclideanSpace_fin,div_pow]
      rw [hn,pow_add,pow_add]
      field_simp [hr.1.ne',hS.ne',hv.ne']
    · exact ball_ratio_tendsto_zero_outside_support μ hK hμ hxK
  have hzero := measure_zero_of_vanishing_ball_ratio μ
    (A := closedBall 0 a) measure_closedBall_lt_top.ne hratio
  have hh : μ.real (closedBall (0:Euclidean m) a) = 0 := by
    simp only [Measure.real,hzero,ENNReal.toReal_zero]
  exact hpos.ne' hh

end RegularPointCoordinates

end

end OAI
