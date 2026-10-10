import OAI.Analysis.CircleDomains.Modulus.UngatedBarrier
import OAI.Analysis.CircleDomains.Selection.RealCoordinateFamily
import OAI.Analysis.CircleDomains.Modulus.BandBudgetNorm

namespace OAI

/-! The constructed ungated barrier controls the ordinary gradient-plus-band
norm used by the limiting line-payment estimate. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]

namespace CompatibleRealBarrier
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
  {previous : ℕ → PhysicalRealCoordinate d π} {flags EStar : Set Sphere}
  {regions : ℕ → Set Sphere} {f : d.quotientDomain → Sphere}

theorem controlledSize_ne_top
    {W : Set Sphere} (R : CompatibleRealBarrier d π previous flags EStar regions f W) :
    R.controlledSize ≠ ∞ := by
  apply ENNReal.add_ne_top.mpr
  refine ⟨ENNReal.ofReal_ne_top, ?_⟩
  exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) R.weight_finite.ne

theorem ordinary_norm_le_controlledSize
    (R : CompatibleRealBarrier d π previous flags EStar regions f univ)
    (hclosure : d.dust ⊆ closure d.quotientDomain)
    {A : Type*} (a : A → Sphere) (ha : Injective a) (haB : range a ⊆ d.dust) :
    Real.sqrt (∫ x in FiniteTransfer.realChartDomain d.physicalDomain,
      FiniteTransfer.gradientEnergy R.coordinate.physical
        (fun z => FiniteTransfer.sphericalMetricFactor z • 1) x) +
    Real.sqrt (∑' s, (limsup R.coordinate.quotient (𝓝[d.quotientDomain] (a s)) -
      liminf R.coordinate.quotient (𝓝[d.quotientDomain] (a s))) ^ 2) ≤
      R.controlledSize.toReal := by
  have hunit (x : Sphere) (_ : x ∈ d.quotientDomain) : |R.coordinate.quotient x| ≤ 1 := by
    rw [abs_of_nonneg (R.coordinate.quotient_unit x).1]
    exact (R.coordinate.quotient_unit x).2
  have hnorm := real_square_norm_le_counting
    (fun s => limsup R.coordinate.quotient (𝓝[d.quotientDomain] (a s)) -
      liminf R.coordinate.quotient (𝓝[d.quotientDomain] (a s))) R.weight a ha
    (fun s => boundary_width_nonneg hunit (hclosure (haB (mem_range_self s))))
    (fun s => R.band_bound (a s) (haB (mem_range_self s))) R.weight_finite
  rw [R.controlledSize_of_univ, ENNReal.toReal_add ENNReal.ofReal_ne_top
    (show countingSquareNorm R.weight ≠ ∞ from
      ENNReal.rpow_ne_top_of_nonneg (by norm_num) R.weight_finite.ne),
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
  exact add_le_add le_rfl hnorm

end CompatibleRealBarrier
end CircleDomainRigidity

end

end OAI
