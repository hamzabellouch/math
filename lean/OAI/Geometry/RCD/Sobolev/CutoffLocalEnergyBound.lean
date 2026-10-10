import OAI.Geometry.RCD.Sobolev.GoodLaplacianCutoff

namespace OAI

/-! # A local gradient cap bounds the full cutoff energy -/

open Set Filter Metric MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (Q : QuadraticCheegerEnergy μ) [IsFiniteMeasureOnCompacts μ]

theorem GoodLaplacianCutoff.local_energy_le {p : X} {r C b L : ℝ}
    (χ : GoodLaplacianCutoff μ Q p r C) (hb : 2*r<b)
    (u : SobolevSpace μ Q)
    (hL : ∀ᵐ x ∂μ.restrict (ball p b), localGamma μ Q u u x≤L^2) :
    weightedGamma μ Q χ.weight u u≤L^2*μ.real (ball p b) := by
  have hloc : weightedGamma μ Q χ.weight u u=
      ∫ x in ball p b, χ.weight x*localGamma μ Q u u x ∂μ := by
    symm
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    apply Eventually.of_forall
    intro x hx
    have hd : b≤dist p x := by simpa only [mem_ball,dist_comm,not_lt] using hx
    rw [χ.zero x (hb.trans_le hd),zero_mul]
  rw [hloc]
  calc
    _ ≤ ∫ _x in ball p b, L^2 ∂μ := by
      apply integral_mono_ae
        (((localGamma_memL1 μ Q u u).bdd_mul χ.weight.continuous.aestronglyMeasurable
          (Eventually.of_forall χ.weight.norm_coe_le_norm)).integrableOn)
        (integrableOn_const (measure_ball_lt_top.ne))
      filter_upwards [hL,ae_restrict_of_ae (localGamma_self μ Q u)] with x hx hself
      have h0 : 0≤localGamma μ Q u u x := by rw [hself]; positivity
      exact (mul_le_of_le_one_left h0 (χ.bounds x).2).trans hx
    _ = _ := by rw [setIntegral_const,smul_eq_mul,mul_comm]

end RegularPointCoordinates

end

end OAI
