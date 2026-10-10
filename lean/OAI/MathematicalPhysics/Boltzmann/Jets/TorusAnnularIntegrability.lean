import OAI.MathematicalPhysics.Boltzmann.Jets.AnnularEnvelopes
import OAI.MathematicalPhysics.Boltzmann.Jets.JetPeriodicDatum

namespace OAI

/-! # Lifting annular integrable bounds to time times the spatial torus -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.AnnularEnvelope

def timePositionVolume (T : ℝ) : Measure (ℝ × Position) :=
  (volume.restrict (Icc (0:ℝ) T)).prod volume

def torusChart (u : ℝ × Position) : ℝ × Transverse :=
  (u.1,transverse (TorusChart.representative u.2))

theorem torusChart_measurable : Measurable torusChart := by
  have hm := TorusChart.representative_measurePreserving.measurable
  have ht : Measurable transverse := JetPeriodicDatum.spatialMap_measurePreserving.measurable.fst
  exact measurable_fst.prodMk (ht.comp (hm.comp measurable_snd))

theorem torus_lift_integrable {T : ℝ} {G : ℝ × Transverse → ℝ}
    (hG : Integrable G (timeSpaceVolume T)) :
    Integrable (fun u : ℝ × Position => G (torusChart u)) (timePositionVolume T) := by
  let μt : Measure ℝ := volume.restrict (Icc (0:ℝ) T)
  let a : ℝ → ℝ := (Icc (-1:ℝ) 1).indicator (fun _ => (1:ℝ))
  have ha : Integrable a := (integrable_indicator_iff measurableSet_Icc).mpr
    (integrableOn_const measure_Icc_lt_top.ne)
  have hprod : Integrable (fun z : (ℝ × Transverse) × ℝ => G z.1*a z.2)
      ((μt.prod volume).prod volume) := hG.mul_prod ha
  have he := (measurePreserving_prodAssoc μt (volume : Measure Transverse) (volume : Measure ℝ)).symm
  have hs := he.integrable_comp_of_integrable hprod
  have hv := ((MeasurePreserving.id μt).prod JetPeriodicDatum.spatialMap_measurePreserving).integrable_comp_of_integrable hs
  have hvr := hv.mono_measure (Measure.prod_mono le_rfl
    (Measure.restrict_le_self (μ := (volume : Measure Velocity)) (s := TorusChart.cube)))
  have hp := ((MeasurePreserving.id μt).prod TorusChart.representative_measurePreserving).integrable_comp_of_integrable hvr
  apply hp.congr
  filter_upwards [] with u
  have hc := TorusChart.representative_mem u.2 (Fin.last 2)
  have hac : axial (TorusChart.representative u.2) ∈ Icc (-1:ℝ) 1 := by
    change -(1/2:ℝ) < axial (TorusChart.representative u.2) ∧ axial (TorusChart.representative u.2) ≤ 1/2 at hc
    exact ⟨by linarith [hc.1],by linarith [hc.2]⟩
  change G (u.1,transverse (TorusChart.representative u.2))*a (axial (TorusChart.representative u.2)) = _
  rw [show a (axial (TorusChart.representative u.2)) = 1 from indicator_of_mem hac _,mul_one]
  rfl

theorem torusChart_mem_cell (u : ℝ × Position) : torusChart u ∈ cell 2 := by
  have hc := TorusChart.representative_mem u.2
  have h0 : |TorusChart.representative u.2 0| ≤ 1/2 := abs_le.mpr ⟨(hc 0).1.le,(hc 0).2⟩
  have h1 : |TorusChart.representative u.2 1| ≤ 1/2 := abs_le.mpr ⟨(hc 1).1.le,(hc 1).2⟩
  have hs0 : (TorusChart.representative u.2 0)^2 ≤ (1/2:ℝ)^2  := by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by norm_num)).mpr h0
  have hs1 : (TorusChart.representative u.2 1)^2 ≤ (1/2:ℝ)^2  := by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by norm_num)).mpr h1
  have hn := EuclideanSpace.real_norm_sq_eq (transverse (TorusChart.representative u.2))
  simp only [Fin.sum_univ_two,transverse,PiLp.toLp_apply] at hn
  change ‖transverse (TorusChart.representative u.2)‖^2 =
    (TorusChart.representative u.2 0)^2+(TorusChart.representative u.2 1)^2 at hn
  change transverse (TorusChart.representative u.2) ∈ Metric.ball 0 2
  rw [Metric.mem_ball,dist_zero_right]
  nlinarith [norm_nonneg (transverse (TorusChart.representative u.2))]

end BoltzmannNonuniqueness.AnnularEnvelope

end

end OAI
