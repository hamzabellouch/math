import OAI.Analysis.CircleDomains.Selection.ScalarLocalizedRange
import OAI.Analysis.CircleDomains.Topology.RangePreservingCutoff

namespace OAI

/-! A strict bound on the scalar's smooth image inside a bounded Jordan
region also bounds its weak representative on the whole closed region. -/
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
  {Q : Fin m → PhysicalRealCoordinate d π} {R : RetainedRealCircleModel d π Q}
namespace ScalarWeakLimit
variable {i : Fin m} (W : R.ScalarWeakLimit i)

 theorem le_on_closed_region (hsch : PlanarSchoenflies) (hG : IsOpen d.physicalDomain)
    {O : Set ℂ} (hO : IsOpen O) (hK : IsCompact (closure O))
    (hfront : frontier O ⊆ R.limit.function '' (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain))
    {b : ℝ} (hb : 0 ≤ b)
    (hbound : ∀ z ∈ closure O,
      z ∈ R.limit.function '' (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain) →
      R.imageScalar i z < b) :
    ∀ᵐ z ∂volume, z ∈ closure O → W.scalar z ≤ b := by
  have hD := (R.limit.plane_open_embedding hG).2.1 _
    (hG.preimage OnePoint.continuous_coe) (Subset.refl _)
  obtain ⟨η, hη, hs, hu, hone, hd, hr⟩ := exists_range_preserving_cutoff hD hO hK hfront
    (R.imageScalar_contDiffOn hG i).continuousOn hbound
  let e := complexPlaneCoordinates
  have hηE : ContDiff ℝ (⊤ : ℕ∞) (η ∘ e) := hη.comp e.contDiff
  have hdE (x : EuclideanPlane)
      (hx : e x ∉ R.limit.function '' (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain)) :
      fderiv ℝ (η ∘ e) x = 0 := by
    rw [fderiv_comp x (hη.differentiable (by simp) _ ) e.differentiableAt, hd _ hx]
    simp
  have he := W.le_on_cutoff_plateau hsch hG hηE (hs.comp_homeomorph e.toHomeomorph)
    (fun x => hu (e x)) hdE hb (fun x hx hne => hr (e x) hx hne)
  have hm := complexPlaneCoordinates_measurePreserving.symm e.toHomeomorph.toMeasurableEquiv
  filter_upwards [hm.quasiMeasurePreserving.ae he] with z hz hzO
  have honez : η z = 1 := hone.self_of_nhdsSet z hzO
  change η (e (e.symm z)) = 1 → W.scalar (e (e.symm z)) ≤ b at hz
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using hz
    (by simpa only [ContinuousLinearEquiv.apply_symm_apply] using honez)

end ScalarWeakLimit
end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
