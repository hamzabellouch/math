import OAI.Geometry.RCD.Metric.PowerBallDimension

namespace OAI

/-! # Full Euclidean image from exact ball masses and total mass saturation -/

open Set Metric Filter MeasureTheory
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates

theorem ball_subset_of_power_ball_mass {n : ℕ} (hn : 0 < n)
    (μ : Measure (Euclidean n)) [IsFiniteMeasure μ] {K : Set (Euclidean n)}
    (hK : IsClosed K) (hμ : ∀ᵐ x ∂μ, x ∈ K)
    {a S : ℝ} (ha : 0 < a) (hS : 0 < S)
    (hcenter : μ.real (ball (0:Euclidean n) a) = (a/S)^n)
    (hmass : ∀ x ∈ K ∩ closedBall (0:Euclidean n) a,
      ∀ r : ℝ, 0 < r → r ≤ a → μ.real (closedBall x r) = (r/S)^n) :
    ball (0:Euclidean n) a ⊆ K := by
  let U := ball (0:Euclidean n) a
  let c : ℝ≥0 := ⟨(S^n*volume.real (ball (0:Euclidean n) 1))⁻¹,by positivity⟩
  have hv : 0 < volume.real (ball (0:Euclidean n) 1) :=
    ENNReal.toReal_pos (measure_ball_pos volume _ zero_lt_one).ne' measure_ball_ne_top
  have hc : 0 < c := by change (0:ℝ) < _; positivity
  have hcost (r : ℝ) (hr : 0 ≤ r) (x : Euclidean n) :
      (r/S)^n = (c:ℝ)*volume.real (closedBall x r) := by
    rw [euclidean_closedBall_real hn x hr,div_pow]
    change r^n / S^n = (S^n*volume.real (ball (0:Euclidean n) 1))⁻¹ *
      (r^n*volume.real (ball (0:Euclidean n) 1))
    field_simp [hS.ne',hv.ne']
  have hb : ∀ x ∈ U, ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, 0 < r → r ≤ R →
      μ (closedBall x r) ≤ (c:ℝ≥0∞)*volume (closedBall x r) := by
    intro x hx
    by_cases hxK : x ∈ K
    · refine ⟨a,ha,?_⟩
      intro r hr hra
      have hh := (hmass x ⟨hxK,ball_subset_closedBall hx⟩ r hr hra).trans (hcost r hr.le x)
      apply (ENNReal.toReal_le_toReal (measure_ne_top μ _)
        (ENNReal.mul_ne_top ENNReal.coe_ne_top measure_closedBall_lt_top.ne)).mp
      simpa only [ENNReal.toReal_mul,ENNReal.coe_toReal,Measure.real] using hh.le
    · obtain ⟨R,hR,hball⟩ := Metric.isOpen_iff.mp hK.isOpen_compl x hxK
      refine ⟨R/2,by positivity,?_⟩
      intro r _ hrR
      have hnull : μ (closedBall x r) = 0 := measure_mono_null
        ((closedBall_subset_ball (by linarith)).trans hball) (ae_iff.mp hμ)
      rw [hnull]
      exact bot_le
  have hle : μ.restrict U ≤ (c • volume).restrict U := by
    intro A
    rw [Measure.restrict_apply' measurableSet_ball,Measure.restrict_apply' measurableSet_ball]
    apply local_ball_measure_order_at μ c
    intro x hx
    exact hb x hx.2
  have heq : μ.restrict U = (c • volume).restrict U := by
    apply Measure.eq_of_le_of_measure_univ_eq hle
    simp only [Measure.restrict_apply_univ,Measure.coe_nnreal_smul_apply]
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ U)
      (ENNReal.mul_ne_top ENNReal.coe_ne_top measure_ball_ne_top)).mp
    simp only [ENNReal.toReal_mul,ENNReal.coe_toReal]
    change μ.real U = (c:ℝ)*volume.real U
    rw [hcenter,euclidean_ball_real hn 0 ha.le,div_pow]
    change a^n / S^n = (S^n*volume.real (ball (0:Euclidean n) 1))⁻¹ *
      (a^n*volume.real (ball (0:Euclidean n) 1))
    field_simp [hS.ne',hv.ne']
  intro x hx
  by_contra hxK
  let A := U ∩ Kᶜ
  have hAnull : μ A = 0 := measure_mono_null inter_subset_right (ae_iff.mp hμ)
  have he := congrArg (fun ν : Measure (Euclidean n) => ν A) heq
  have hAU : A ∩ U = A := inter_eq_self_of_subset_left inter_subset_left
  rw [Measure.restrict_apply' measurableSet_ball,Measure.restrict_apply' measurableSet_ball,
    hAU,Measure.coe_nnreal_smul_apply,hAnull] at he
  have hAp : 0 < volume A := (isOpen_ball.inter hK.isOpen_compl).measure_pos volume ⟨x,hx,hxK⟩
  exact (mul_ne_zero (ENNReal.coe_ne_zero.mpr hc.ne') hAp.ne') he.symm

end RegularPointCoordinates

end

end OAI
