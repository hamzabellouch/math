import Mathlib
import OAI.Probability.GaussianRegression.Main
import OAI.Probability.MemoryPrecision.KernelModel
import OAI.Probability.MemoryPrecision.WeightedImage
import OAI.Probability.MemoryPrecision.WeightedSelection

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision
abbrev Sphere (d : ℕ) := Metric.sphere (0 : Space d) 1
def SpherePrior (d : ℕ) : Measure (Sphere d) :=
  MemoryPrecision.Kernel.UniformSphere d

def SphereBallBound {d : ℕ} (h : Sphere d → ℝ≥0∞) (H α : ℝ) : Prop :=
  ∀ z : Space d, ∀ r : ℝ, 0 < r →
    (∫⁻ s in {s : Sphere d | dist s.val z ≤ r}, h s ∂SpherePrior d) ≤
      ENNReal.ofReal (H * r^α)
def SphereBlock {d m N : ℕ} (h : Fin N → Sphere d → ℝ≥0∞)
    (g : Fin N → ((Fin m → Space d) × (Fin m → ℝ)) → ℝ≥0∞)
    (s : Sphere d) : ℝ≥0∞ :=
  WeightedBlock Subtype.val h g s
def CoefficientStepStatement : Prop :=
  let two : ℝ := @OfNat.ofNat ℝ 2 (@instOfNatAtLeastTwo ℝ 2 Real.commRing.toNatCast
    (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  ∃ C : ℝ, 1 ≤ C ∧ ∀ d m N : ℕ, 16 ≤ d →
    1 ≤ m → m ≤ d/8 → 1 ≤ N →
    ∀ α H : ℝ, ((d:ℝ)-1)/two ≤ α → α ≤ (d:ℝ)/two → 0 < H →
    ∀ h : Fin N → Sphere d → ℝ≥0∞,
      (∀ w, Measurable (h w)) → (∀ w s, h w s ≤ 1) →
      (∀ w, SphereBallBound (h w) H α) →
    ∀ g : Fin N → ((Fin m → Space d) × (Fin m → ℝ)) → ℝ≥0∞,
      (∀ w, Measurable (g w)) → (∀ x, ∑ w, g w x ≤ 1) →
      SphereBallBound (SphereBlock h g) (C^d * (N:ℝ)^(1/((d/8:ℕ):ℝ)) * H) α

theorem coefficient_step : CoefficientStepStatement := by
  refine ⟨1344, by norm_num, ?_⟩
  intro d m N hd hm hmp hN α H hαlo hαhi hH h hh hh1 hb g hg hgsum z r hr
  have : NeZero d := ⟨by omega⟩
  have : IsProbabilityMeasure (SpherePrior d) :=
    (show IsProbabilityMeasure (NoiselessRegression.sphereLaw (E := Space d)) from inferInstance)
  let ν (w : Fin N) := ((SpherePrior d).withDensity (h w)).map Subtype.val
  let (w : Fin N) : IsFiniteMeasure (ν w) :=
    weighted_image_finite (SpherePrior d) Subtype.val (h w) (hh1 w)
  have hν (w) : AmbientBallBound (ν w) H α := by
    intro x ρ hρ
    rw [show ν w = ((SpherePrior d).withDensity (h w)).map Subtype.val from rfl,
      weighted_image_ball _ measurable_subtype_coe]
    exact hb w x ρ hρ
  have hp : 2 ≤ d/8 := by omega
  have hmd : m ≤ d := hmp.trans (Nat.div_le_self _ _)
  have hgap : (m:ℝ)+((d/8:ℕ):ℝ)-2 < α := by
    have hm' : (m:ℝ) ≤ (d/8:ℕ) := by exact_mod_cast hmp
    have hp' : ((d/8:ℕ):ℝ)*8 ≤ d := by exact_mod_cast Nat.div_mul_le_self d 8
    have hd' : (16:ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hJ := fun j hj => (specialized_J_bound d m (d/8) hd rfl hm hmp α hαlo hαhi j hj).2.2
  have hsel := localized_weighted_selection ν hp hm hmd (by norm_num : (1:ℝ) ≤ 7)
    hH hgap hJ hν g hg hgsum z hr
  have he := weightedBlock_mass_identity (SpherePrior d) measurable_subtype_coe hh hh1 hg
    (show MeasurableSet (Metric.closedBall z r) from Metric.isClosed_closedBall.measurableSet)
  change (∫⁻ s in Subtype.val ⁻¹' Metric.closedBall z r,
    WeightedBlock Subtype.val h g s ∂SpherePrior d) ≤ _
  rw [he]
  convert hsel using 1
  norm_num [ν, mul_assoc]

end MemoryPrecision


end

end OAI
