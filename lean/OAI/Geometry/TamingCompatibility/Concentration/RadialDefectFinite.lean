import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.UnitTransverseIntegrable

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.Hermitian
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory RadialPotential
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

omit [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] in
lemma unitRadialDefect_zero_of_radius (p : X) (b : Space)
    {u : MetricUnit (hermitianMetric J α hs ht)} (hu : unitRadialRadius J α hs ht p b u = 0) :
    unitRadialDefect J α hs ht p b u = 0 := by
  have hz : hermitianGraph (coordinateJ J p b) (unitChartBase J α hs ht p u-b) = 0 :=
    norm_eq_zero.mp hu
  simp only [unitRadialDefect,hermitianDefect,hz,norm_zero,zero_pow (by norm_num : 2 ≠ 0),
    zero_mul,inner_zero_left,sub_zero]

omit [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] in
lemma smoothUnitDefect_tendsto (p : X) (b : Space) (r : ℝ)
    (u : MetricUnit (hermitianMetric J α hs ht)) :
    Tendsto (fun s : ℝ => smoothUnitDefect J α hs ht p b r s u)
      (𝓝 0) (𝓝 (smoothUnitDefect J α hs ht p b r 0 u)) := by
  by_cases hu : u ∈ unitChartDomain J α hs ht p (Metric.closedBall b r)
  · simp only [smoothUnitDefect,Set.indicator_of_mem hu]
    by_cases hz : unitRadialRadius J α hs ht p b u = 0
    · simp only [unitRadialDefect_zero_of_radius J α hs ht p b hz,mul_zero,zero_div]
      exact tendsto_const_nhds
    · have hh := (tendsto_const_nhds (x := (2 : ℝ) * unitRadialDefect J α hs ht p b u)).div
        ((((tendsto_id : Tendsto (fun s : ℝ => s) (𝓝 0) (𝓝 0)).pow 2).add_const ((unitRadialRadius J α hs ht p b u)^2)).pow 2)
        (by simpa only [zero_pow (by norm_num : 2 ≠ 0),zero_add] using pow_ne_zero 2 (pow_ne_zero 2 hz))
      exact hh
  · simp only [smoothUnitDefect,Set.indicator_of_notMem hu]
    exact tendsto_const_nhds

omit [MeasurableSpace X] [BorelSpace X] in

lemma singularDefect_integrable_of_bounds (p : X) (b : Space) {r C : ℝ}
    (hr : 0 < r) (hC : 0 ≤ C)
    (hball : Metric.closedBall b r ⊆ (extChartAt Model p).target)
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
    (hbound : ∀ s ∈ Ioc (0:ℝ) r,
      ∫ u, smoothUnitDefect J α hs ht p b r s u ∂μ ≤ C) :
    Integrable (smoothUnitDefect J α hs ht p b r 0) μ ∧
      ∫ u, smoothUnitDefect J α hs ht p b r 0 u ∂μ ≤ C := by
  let seq : ℕ → ℝ := fun n => r/(n+1)
  have hseq (n : ℕ) : seq n ∈ Ioc (0:ℝ) r := by
    dsimp [seq]
    constructor
    · positivity
    · apply (div_le_iff₀ (by positivity : 0 < (n:ℝ)+1)).mpr
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hseq0 : Tendsto seq atTop (𝓝 0) := by
    have hh : Tendsto (fun n : ℕ => (n:ℝ)+1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [seq, Function.comp_apply,div_eq_mul_inv,mul_zero] using
      (tendsto_inv_atTop_zero.comp hh).const_mul r
  have hb : b ∈ (extChartAt Model p).target := hball (Metric.mem_closedBall_self hr.le)
  exact integrable_nonneg_limit_of_uniform_integral hC
    (fun n => smoothUnitDefect_integrable J α hs ht p b r (hseq n).1 hball μ)
    (fun n u => smoothUnitDefect_nonneg J α hs ht p hb r (seq n) u)
    (fun n => hbound (seq n) (hseq n))
    (fun u => (smoothUnitDefect_tendsto J α hs ht p b r u).comp hseq0)

end TamingCompatibility.GeometricHilbert.Hermitian

end
end

end OAI
