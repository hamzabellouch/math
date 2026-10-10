import OAI.Analysis.Mahler.FiberHeight
import OAI.Analysis.Mahler.FiberPrimitive
import Mathlib.Analysis.Calculus.Deriv.Inverse

namespace OAI

namespace SymmetricMahler
open Real Complex Set Filter MeasureTheory
open scoped Topology

noncomputable def radialPrimitive (q r₀ m r : ℝ) : ℝ :=
  ∫ t in r₀..r, radialPrimitiveDensity (fiberAngle q) m t

lemma continuousAt_radialPrimitiveDensity {q m r : ℝ} (hr : r ∈ fiberDomain q) :
    ContinuousAt (radialPrimitiveDensity (fiberAngle q) m) r := by
  have hθ := (contDiffAt_fiberAngle hr).continuousAt
  have hs := fiberAngle_spec hr
  have hrpos : 0 < r := hr.1
  have hden : 1-r^2 ≠ 0 := ne_of_gt (by nlinarith [hr.2.1])
  have hB : angularSpeed r (fiberAngle q r) ≠ 0 :=
    (MahlerConformal.B_pos hr.1 hr.2.1 hs.1.1 hs.1.2).ne'
  have hbcont : ContinuousAt (fun t => angularSpeed t (fiberAngle q t)) r := by
    unfold angularSpeed
    fun_prop
  unfold radialPrimitiveDensity
  exact continuousAt_const.mul ((Real.continuousAt_rpow_const r (2*m-1) (Or.inl hrpos.ne')).div hbcont hB)

lemma measurable_radialPrimitiveDensity (q m : ℝ) :
    Measurable (radialPrimitiveDensity (fiberAngle q) m) := by
  have hθ := measurable_fiberAngle q
  unfold radialPrimitiveDensity angularSpeed
  fun_prop

/-- The radial primitive has its defining density as derivative, including
an integrable singular lower endpoint. -/
theorem hasDerivAt_radialPrimitive {q r₀ m r : ℝ} (hm : 2 ≤ m) (hr₀ : 0 ≤ r₀)
    (hq : radialMap r₀ = |q|) (hr : r ∈ Ioo r₀ 1) :
    HasDerivAt (radialPrimitive q r₀ m)
      (radialPrimitiveDensity (fiberAngle q) m r) r := by
  have hi := radial_primitive_integrable (measurable_fiberAngle q) hm hr₀ hr.1.le hr.2
    (fun s hs => fiberAngle_sine_bound hr₀ hq hs)
  exact intervalIntegral.integral_hasDerivAt_right hi
    (measurable_radialPrimitiveDensity q m).stronglyMeasurable.stronglyMeasurableAtFilter
    (continuousAt_radialPrimitiveDensity (mem_fiberDomain_of_basepoint hr₀ hq hr))

/-- Dividing radial density by vertical speed gives the prescribed vertical
derivative. -/
theorem radial_density_div_vertical_speed {q r m : ℝ} (hr : r ∈ fiberDomain q) :
    radialPrimitiveDensity (fiberAngle q) m r / deriv (fiberHeight q) r =
      (4*m/Real.pi)*r^(2*m-2 : ℝ) /
        ‖deriv MahlerConformal.F (MahlerConformal.polar r (fiberAngle q r))‖^2 := by
  have hs := fiberAngle_spec hr
  have hB : MahlerConformal.B r (fiberAngle q r) ≠ 0 :=
    (MahlerConformal.B_pos hr.1 hr.2.1 hs.1.1 hs.1.2).ne'
  have hrne : r ≠ 0 := hr.1.ne'
  have hp : r^(2*m-1 : ℝ)/r = r^(2*m-2 : ℝ) := by
    rw [← rpow_sub_one hrne]
    congr 1
    ring
  rw [(hasDerivAt_fiberHeight hr).deriv]
  change ((4*m/Real.pi)*(r^(2*m-1 : ℝ)/MahlerConformal.B r (fiberAngle q r))) /
      (r*‖deriv MahlerConformal.F (MahlerConformal.polar r (fiberAngle q r))‖^2 /
        MahlerConformal.B r (fiberAngle q r)) = _
  calc
    _ = (4*m/Real.pi)*(r^(2*m-1 : ℝ)/r) /
        ‖deriv MahlerConformal.F (MahlerConformal.polar r (fiberAngle q r))‖^2 := by
      field_simp
    _ = _ := by rw [hp]

end SymmetricMahler

end OAI
