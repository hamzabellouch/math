import OAI.MathematicalPhysics.Boltzmann.Branching.PlaneChart
import OAI.MathematicalPhysics.Boltzmann.Approximation.ColoredDifferenceAlgebra
import OAI.MathematicalPhysics.Boltzmann.Collision.WeightAlgebra

namespace OAI

/-!
# Nonnegative Carleman gain

Gamba, Panferov and Villani, *Upper Maxwellian bounds for the spatially
homogeneous Boltzmann equation*, Arch. Ration. Mech. Anal. 194 (2009),
253–282, Appendix C, Lemma 16 and the hard-sphere remark. The author's
preprint https://www.csun.edu/~panferov/research/umb_5.pdf gives the formula
on pp. 23–24. Their hard-sphere rate is `|g|/(4π)` in outgoing-direction
coordinates. Multiplication by `2π` gives the present absolute-normal
kernel and the coefficient `2` below.

The nonnegative measurable form of that identity is expressed in an explicit
plane chart. Its density formulation includes the plane-chart measure
identification and allows arbitrary nonnegative measurable densities.
-/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.PlaneChart
open scoped ENNReal

namespace BoltzmannNonuniqueness

/-- The nonnegative symmetric gain in the original normal-sphere variables. -/
def nonnegativeGain (f g : Velocity → ℝ≥0∞) (v : Velocity) : ℝ≥0∞ :=
  ∫⁻ p : Velocity × Sphere,
    (ENNReal.ofReal (collisionKernel v p.1 p.2) / 2) *
      (f (scatterLeft v p.1 p.2) * g (scatterRight v p.1 p.2) +
        g (scatterLeft v p.1 p.2) * f (scatterRight v p.1 p.2)) ∂gainPairMeasure

/-- Carleman gain against a possibly singular incoming velocity measure.
The transverse degeneracy set has measure zero for the sheet laws used here. -/
def chartGain (c : Measure Velocity) (h : Velocity → ℝ≥0∞) (v : Velocity) : ℝ≥0∞ :=
  2 * ∫⁻ p : Velocity,
    ENNReal.ofReal (‖normal v p‖⁻¹) *
      ∫⁻ z : ℝ, ∫⁻ s : ℝ, h (chart v p z s) ∂volume ∂volume ∂c

/-- Restriction in the actual incoming velocity and the two chart coordinates. -/
def chartRegionGain (c : Measure Velocity) (h : Velocity → ℝ≥0∞) (v : Velocity)
    (S : Set (Velocity × (ℝ × ℝ))) : ℝ≥0∞ := by
  classical
  exact 2 * ∫⁻ p : Velocity, ENNReal.ofReal (‖normal v p‖⁻¹) *
    ∫⁻ z : ℝ, ∫⁻ s : ℝ, S.indicator
      (fun y => h (chart v y.1 y.2.1 y.2.2)) (p, (z, s)) ∂volume ∂volume ∂c

def normalizedChartGain (c : Measure Velocity) (q : ℝ) (v : Velocity) : ℝ≥0∞ :=
  chartGain c (fun ξ => ENNReal.ofReal (VelocityWeight.H q ξ / VelocityWeight.H q v)) v

def normalizedChartRegionGain (c : Measure Velocity) (q : ℝ) (v : Velocity)
    (S : Set (Velocity × (ℝ × ℝ))) : ℝ≥0∞ :=
  chartRegionGain c (fun ξ => ENNReal.ofReal (VelocityWeight.H q ξ / VelocityWeight.H q v)) v S

/-- The algebraic estimate applies to every nondegenerate point of the actual chart. -/
theorem chart_weight_ratio_le (q : ℝ) (v p : Velocity) (z s : ℝ)
    (hn : normal v p ≠ 0) :
    VelocityWeight.H q (chart v p z s) / VelocityWeight.H q v ≤
      VelocityWeight.tiltConstant *
        Real.exp (2 * ‖p‖ ^ 2 - ‖companionVelocity p (chart v p z s) v‖ ^ 2) *
        (VelocityWeight.W q (chart v p z s) / VelocityWeight.W q v) :=
  VelocityWeight.collision_weight_ratio_le q p (chart v p z s) v (chart_on_plane v p z s hn)

namespace Published

/-- The application-specific nonnegative form of the published Carleman identity.
For densities the zero transverse-normal set is Lebesgue null. The statement
does not assert equality for arbitrary singular incoming measures. -/
def GPV2009CarlemanInput : Prop :=
  ∀ f g : Velocity → ℝ≥0∞, Measurable f → Measurable g →
    ∀ᵐ v : Velocity ∂volume,
      nonnegativeGain f g v = chartGain (volume.withDensity f) g v

end Published

theorem chartGain_mono_right {c : Measure Velocity} {h k : Velocity → ℝ≥0∞}
    (hkh : ∀ ξ, h ξ ≤ k ξ) (v : Velocity) : chartGain c h v ≤ chartGain c k v := by
  unfold chartGain
  gcongr
  exact hkh _

theorem chartGain_mono_measure {c d : Measure Velocity} (hcd : c ≤ d)
    (h : Velocity → ℝ≥0∞) (v : Velocity) : chartGain c h v ≤ chartGain d h v := by
  unfold chartGain
  exact mul_le_mul' (le_rfl : (2 : ℝ≥0∞) ≤ 2)
    (lintegral_mono' hcd (fun _ => le_rfl))

theorem chartGain_add_measure (c d : Measure Velocity) (h : Velocity → ℝ≥0∞)
    (v : Velocity) : chartGain (c + d) h v = chartGain c h v + chartGain d h v := by
  unfold chartGain
  rw [lintegral_add_measure, mul_add]

theorem chartGain_smul_measure (a : ℝ≥0∞) (c : Measure Velocity)
    (h : Velocity → ℝ≥0∞) (v : Velocity) :
    chartGain (a • c) h v = a * chartGain c h v := by
  unfold chartGain
  rw [lintegral_smul_measure]
  simp only [smul_eq_mul]
  ac_rfl

/-- A bound proved for the explicit chart gain transfers to the original gain
under the stated published input. -/
theorem nonnegativeGain_le_of_chartGain
    (hcarleman : Published.GPV2009CarlemanInput)
    {f g : Velocity → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    {B : Velocity → ℝ≥0∞}
    (hB : ∀ᵐ v : Velocity ∂volume, chartGain (volume.withDensity f) g v ≤ B v) :
    ∀ᵐ v : Velocity ∂volume, nonnegativeGain f g v ≤ B v := by
  filter_upwards [hcarleman f g hf hg, hB] with v hv hb
  rwa [hv]

end BoltzmannNonuniqueness

end

end OAI
