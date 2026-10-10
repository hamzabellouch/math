import Mathlib
import OAI.Probability.GaussianRegression.Main
import OAI.Probability.MemoryPrecision.DensityUniqueness

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision
open NoiselessRegression

def RadialMixtureRepresentation (m : ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ →
    (∀ r : ℝ, 0 < r → 0 ≤ RadialMixture m δ r) ∧
    Measurable (RadialMixture m δ) ∧
    (∫ r in Set.Ioi 0, RadialMixture m δ r) = 1 ∧
    (∀ y : Space m, GaussianKernel m δ y =
      ∫ r in Set.Ioi ‖y‖, RadialMixture m δ r / (UnitBallVolume m * r^m))

def FullRankDensityFormula {d : ℕ}
    (μ : @Measure (Space d)
      (WithLp.measurableSpace
        (@OfNat.ofNat ℝ≥0∞ 2
          (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
            (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))) (Fin d → ℝ)))
    (m : ℕ) : Prop :=
  let exponent : ℝ≥0∞ := @OfNat.ofNat ℝ≥0∞ 2
    (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
      (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  ∀ A : Fin m → Space d,
    @LinearIndependent (Fin m) ℝ (Space d) A Real.commRing.toSemiring
      (WithLp.instAddCommGroup exponent (Fin d → ℝ)).toAddCommMonoid
      (WithLp.instModule (p := exponent) (K := ℝ) (V := Fin d → ℝ)) →
    (volume : Measure (Fin m → ℝ)).withDensity
      (fun y => ENNReal.ofReal (PointwiseDensity μ m (A,y))) =
      @Measure.map (Space d) (Fin m → ℝ)
        (WithLp.measurableSpace exponent (Fin d → ℝ)) inferInstance
        (fun signal => fun index => @inner ℝ (Space d)
          (@InnerProductSpace.toInner ℝ (Space d) _
            (PiLp.seminormedAddCommGroup exponent (fun _ : Fin d => ℝ))
            (PiLp.innerProductSpace (𝕜 := ℝ) (fun _ : Fin d => ℝ)))
          signal (A index)) μ

def PointwiseDensityProperties {d : ℕ}
    (μ : @Measure (Space d)
      (WithLp.measurableSpace
        (@OfNat.ofNat ℝ≥0∞ 2
          (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
            (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))) (Fin d → ℝ)))
    (m p : ℕ) (H β R : ℝ) : Prop :=
  letI : MeasurableSpace (Space d) := WithLp.measurableSpace
    (@OfNat.ofNat ℝ≥0∞ 2
      (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
        (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))) (Fin d → ℝ)
  let reference : Measure ((Fin m → Space d) × (Fin m → ℝ)) := MatrixLabelReference d m
  RadialMixtureRepresentation m ∧
  (∀ x, 0 ≤ PointwiseDensity μ m x) ∧
  Measurable (PointwiseDensity μ m) ∧
  FullRankDensityFormula μ m ∧
  reference.withDensity (fun x => ENNReal.ofReal (PointwiseDensity μ m x)) =
    ProjectionLaw μ m ∧
  (∀ F : ((Fin m → Space d) × (Fin m → ℝ)) → ℝ,
    Measurable F → (∀ x, 0 ≤ F x) →
    reference.withDensity (fun x => ENNReal.ofReal (F x)) =
      ProjectionLaw μ m → PointwiseDensity μ m =ᵐ[reference] F) ∧
  (∫⁻ x, ENNReal.ofReal (PointwiseDensity μ m x)^p ∂reference) ≤
    ENNReal.ofReal (ProjectionNormScale m p H β R)^p

def PointwiseDensityStatement : Prop :=
  let two : ℝ := @OfNat.ofNat ℝ 2 (@instOfNatAtLeastTwo ℝ 2 Real.commRing.toNatCast
    (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  let exponent : ℝ≥0∞ := @OfNat.ofNat ℝ≥0∞ 2
    (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
      (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  ∀ d m p : ℕ, 2 ≤ d → 1 ≤ m → m < d → 2 ≤ p →
  ∀ β H R : ℝ, (m : ℝ)+(p : ℝ)-two < β → 0 < H → 0 < R →
  ∀ z : Space d,
  ∀ μ : @Measure (Space d) (WithLp.measurableSpace exponent (Fin d → ℝ)),
    IsFiniteMeasure μ →
    @Measure.support (Space d)
      (PiLp.topologicalSpace (p := exponent) (β := fun _ : Fin d => ℝ))
      (WithLp.measurableSpace exponent (Fin d → ℝ)) μ ⊆
      @Metric.closedBall (Space d)
        (PiLp.instPseudoMetricSpace (p := exponent) (β := fun _ : Fin d => ℝ)) z R →
    AmbientBallBound μ H β →
    μ ≪ UniformSphere d → PointwiseDensityProperties μ m p H β R

theorem pointwise_density : PointwiseDensityStatement := by
  intro d m p hd hm hmd hp β H R hgap hH hR z μ hμ hs hb hac
  let : IsFiniteMeasure μ := hμ
  obtain ⟨F,hFm,hF0,hden,hFs,hFnorm⟩ :=
    exact_finite_density d m p hp hm β H R hgap hH hR z μ hs hb
  have he := pointwiseDensity_ae_eq hm μ F hFm hF0 hden
  refine ⟨?_, PointwiseDensity_nonneg μ m, measurable_PointwiseDensity μ m,
    ?_, ?_, pointwiseDensity_ae_eq hm μ, ?_⟩
  · intro δ hδ
    exact ⟨fun r hr => radialMixture_nonneg m δ hr, radialMixture_measurable m δ,
      radialMixture_integral m hm hδ, radialMixture_tail m hm hδ⟩
  · intro A hA
    exact pointwiseDensity_fullRank hd hm hmd μ hac A hA
  · exact (withDensity_congr_ae (he.fun_comp ENNReal.ofReal)).trans hden
  · have hp0 : (p:ℝ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
    have hpE : (p:ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
    have hpow := ENNReal.rpow_le_rpow hFnorm (show 0 ≤ (p:ℝ) by positivity)
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpE (by finiteness)
      hFm.aestronglyMeasurable] at hpow
    simp only [ENNReal.toReal_natCast] at hpow
    rw [← ENNReal.rpow_mul, one_div_mul_cancel hp0, ENNReal.rpow_one] at hpow
    simp only [ENNReal.rpow_natCast] at hpow
    have hi : (fun x => ENNReal.ofReal (PointwiseDensity μ m x)^p) =ᵐ[MatrixLabelReference d m]
        (fun x => ‖F x‖ₑ^p) := by
      filter_upwards [he] with x hx
      rw [hx, Real.enorm_eq_ofReal (hF0 x)]
    rw [lintegral_congr_ae hi]
    exact hpow
end MemoryPrecision


end

end OAI
