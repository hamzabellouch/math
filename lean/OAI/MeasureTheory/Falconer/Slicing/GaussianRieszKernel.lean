import OAI.MeasureTheory.Falconer.Recursion.PointRieszPotential
import OAI.MeasureTheory.Falconer.Slicing.GaussianRowMap

namespace OAI

/-! # Gaussian projection of a fixed vector: small balls and inverse moments -/
namespace Falconer
open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d m : ℕ}

@[fun_prop] theorem gaussianRowMap_joint_continuous :
    Continuous (fun p : (Fin m → Space d) × Space d => gaussianRowMap p.1 p.2) := by
  change Continuous (fun p : (Fin m → Space d) × Space d =>
    WithLp.toLp 2 (fun i => inner ℝ (p.1 i) p.2))
  apply (PiLp.continuous_toLp 2 _).comp
  exact continuous_pi (fun i => ((continuous_apply i).comp continuous_fst).inner continuous_snd)

theorem gaussianRowMap_parameter_measurable (z : Space d) :
    Measurable (fun A : Fin m → Space d => gaussianRowMap A z) :=
  (gaussianRowMap_joint_continuous.comp (continuous_id.prodMk continuous_const)).measurable

theorem gaussianRows_image_small_ball {w : Space d} (hw : ‖w‖ = 1)
    {r : ℝ} (hr : 0 < r) :
    gaussianRows d m {A | gaussianRowMap A w ∈ ball 0 r} ≤
      ENNReal.ofReal ((gaussianBandConstant^m)*r^(m:ℝ)) := by
  calc
    _ ≤ gaussianRows d m {A | ∀ i, |inner ℝ w (A i)| ≤ r} := by
      apply measure_mono
      intro A hA i
      have hb : ‖gaussianRowMap A w‖ < r := by simpa using hA
      have hi := PiLp.norm_apply_le (gaussianRowMap A w) i
      simpa only [gaussianRowMap_apply,Real.norm_eq_abs] using hi.trans hb.le
    _ ≤ ENNReal.ofReal ((gaussianBandConstant*r)^m) := gaussianRows_one_band hw hr.le
    _ = _ := by rw [mul_pow,Real.rpow_natCast]

theorem gaussianRows_unit_inverse_moment {w : Space d} (hw : ‖w‖ = 1)
    {u : ℝ} (hu : 0 < u) (hum : u < (m:ℝ)) :
    (∫⁻ A, (edist (0:Space m) (gaussianRowMap A w))^(-u) ∂gaussianRows d m) ≤
      rieszSmallBallBound m (gaussianBandConstant^m) u := by
  let η := (gaussianRows d m).map (fun A => gaussianRowMap A w)
  have hm := gaussianRowMap_parameter_measurable (m := m) w
  have hball : ∀ r > 0, η (ball 0 r) ≤
      ENNReal.ofReal ((gaussianBandConstant^m)*r^(m:ℝ)) := by
    intro r hr
    rw [show η = _ from rfl,Measure.map_apply hm measurableSet_ball]
    exact gaussianRows_image_small_ball hw hr
  have : IsProbabilityMeasure η := (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).mpr inferInstance
  have hh := point_riesz_potential_bound η 0 hu hum hball
  unfold euclideanRieszPotential at hh
  rw [show η = _ from rfl,lintegral_map (by fun_prop) hm] at hh
  exact hh

end Falconer

end OAI
