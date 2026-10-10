import OAI.Analysis.CircleDomains.Modulus.CompatibleLevelBarrier
import OAI.Analysis.CircleDomains.Modulus.BandBudgetNorm
import OAI.Analysis.CircleDomains.Selection.RealCoordinateFamily

namespace OAI

/-! The constructed compatible real barrier controls the localized norm used by the open
map exclusion. Enlarging the omitted penalty set only decreases its Dirichlet payment. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]

namespace CompatibleLevelBarrier
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
  {previous : PriorLevelFamily d.physicalDomain π} {flags EStar : Set Sphere}
  {regions : ℕ → Set Sphere} {f : d.quotientDomain → Sphere} {W : Set Sphere}
  (R : CompatibleLevelBarrier d π previous flags EStar regions f W)

 theorem controlledSize_ne_top : R.controlledSize ≠ ∞ :=
  ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) R.weight_finite.ne⟩

 theorem localized_norm_le_controlledSize
    {P : Set ℂ}
    (hP : (fun x : ℝ × ℝ => π (Complex.equivRealProdCLM.symm x : Sphere)) ⁻¹' R.penalty ⊆
      Complex.equivRealProdCLM '' P) :
    Real.sqrt (∫ x in realChartDomain d.physicalDomain \ (Complex.equivRealProdCLM '' P),
      gradientEnergy R.coordinate.physical (fun z => sphericalMetricFactor z • 1) x) +
      (countingSquareNorm R.weight).toReal ≤ R.controlledSize.toReal := by
  let E := (fun x : ℝ × ℝ => π (Complex.equivRealProdCLM.symm x : Sphere)) ⁻¹' R.penalty
  have hsub : realChartDomain d.physicalDomain \ (Complex.equivRealProdCLM '' P) ⊆
      realChartDomain d.physicalDomain \ E := by
    intro x hx
    exact ⟨hx.1, fun he => hx.2 (hP he)⟩
  have henergy := integrable_gradientEnergy_spherical_of_memLp
    (R.coordinate.physical_energy.mono_measure
      (Measure.restrict_mono_set volume (show realChartDomain d.physicalDomain \ E ⊆
        realChartDomain d.physicalDomain from sdiff_subset)))
  have hi := setIntegral_mono_set henergy
    (Eventually.of_forall fun x => by rw [gradientEnergy_spherical]; positivity)
    (Eventually.of_forall fun x hx => hsub hx)
  change _ ≤ (ENNReal.ofReal _ + countingSquareNorm R.weight).toReal
  have hw : countingSquareNorm R.weight ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) R.weight_finite.ne
  rw [ENNReal.toReal_add ENNReal.ofReal_ne_top hw,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
  exact add_le_add (Real.sqrt_le_sqrt hi) le_rfl

 theorem real_band_norm_le
    (hclosure : d.dust ⊆ closure d.quotientDomain)
    {A : Type*} (a : A → Sphere) (ha : Injective a) (haB : range a ⊆ d.dust) :
    Real.sqrt (∑' s, (limsup R.coordinate.quotient (𝓝[d.quotientDomain] (a s)) -
      liminf R.coordinate.quotient (𝓝[d.quotientDomain] (a s))) ^ 2) ≤
      (countingSquareNorm R.weight).toReal := by
  have hunit (x : Sphere) (_ : x ∈ d.quotientDomain) : |R.coordinate.quotient x| ≤ 1 := by
    rw [abs_of_nonneg (R.coordinate.quotient_unit x).1]
    exact (R.coordinate.quotient_unit x).2
  exact real_square_norm_le_counting _ R.weight a ha
    (fun s => boundary_width_nonneg hunit (hclosure (haB (mem_range_self s))))
    (fun s => R.band_bound (a s) (haB (mem_range_self s))) R.weight_finite

end CompatibleLevelBarrier
end CircleDomainRigidity

end

end OAI
