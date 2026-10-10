import OAI.Analysis.CircleDomains.Uniformization.ScalarPointwiseLimit
import OAI.Analysis.CircleDomains.Sobolev.BoundedWeakIdentification

namespace OAI

/-! Identification of the constructed weak scalar on the actual limiting
circle domain. Positive-area complementary dust is treated separately. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]
namespace RetainedRealCircleModel
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d π} (R : RetainedRealCircleModel d π Q)

def imageScalar (i : Fin m) (z : ℂ) : ℝ :=
  (Q i).physical (Complex.equivRealProdCLM
    (invFunOn R.limit.function (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain) z))

theorem imageScalar_apply (hG : IsOpen d.physicalDomain) (i : Fin m)
    {x : ℂ} (hx : (x : Sphere) ∈ d.physicalDomain) :
    R.imageScalar i (R.limit.function x) = (Q i).physical (Complex.equivRealProdCLM x) := by
  unfold imageScalar
  rw [(R.limit.plane_open_embedding hG).2.2.leftInvOn_invFunOn hx]

theorem ScalarWeakLimit.eq_source_ae {i : Fin m} (W : R.ScalarWeakLimit i)
    (hsch : PlanarSchoenflies) (hG : IsOpen d.physicalDomain) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      z ∈ R.limit.function '' (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain) →
      W.scalar z = R.imageScalar i z := by
  have hS := (R.limit.plane_open_embedding hG).2.1 _
    (hG.preimage OnePoint.continuous_coe) (Subset.refl _)
  have h := ae_eq_on_of_bounded_weak_pointwise
    (μ := planarSphericalArea)
    (fun n => (W.fillings (W.subsequence n)).filled_measurable.aestronglyMeasurable)
    (fun n z => by
      rw [Real.norm_eq_abs, abs_of_nonneg ((W.fillings (W.subsequence n)).filled_mem z).1]
      exact ((W.fillings (W.subsequence n)).filled_mem z).2)
    W.scalar W.scalar_weak hS.measurableSet
    (t := R.imageScalar i)
    (by
      rintro _ ⟨x, hx, rfl⟩
      rw [R.imageScalar_apply hG i hx, (Q i).pullback x hx,
        Real.norm_eq_abs, abs_of_nonneg ((Q i).quotient_unit _).1]
      exact ((Q i).quotient_unit _).2)
    (by
      rintro _ ⟨x, hx, rfl⟩
      rw [R.imageScalar_apply hG i hx]
      exact W.pointwise_on_image R hsch hG hx)
  have habs : (volume : Measure ℂ) ≪ planarSphericalArea :=
    withDensity_absolutelyContinuous'
      continuous_sphericalAreaDensity.measurable.ennreal_ofReal.aemeasurable
      (Eventually.of_forall fun z => (ENNReal.ofReal_pos.mpr (sphericalAreaDensity_pos z)).ne')
  exact habs.ae_le h

end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
