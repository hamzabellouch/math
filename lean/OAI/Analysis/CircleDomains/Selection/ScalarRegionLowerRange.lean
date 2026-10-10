import OAI.Analysis.CircleDomains.Selection.ScalarRegionRange
import OAI.Analysis.CircleDomains.Sobolev.ComplementWeakGradient

namespace OAI

/-! Lower range propagation for the same actual weak scalar. -/
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

 theorem ge_on_closed_region (hsch : PlanarSchoenflies) (hG : IsOpen d.physicalDomain)
    {O : Set ℂ} (hO : IsOpen O) (hK : IsCompact (closure O))
    (hfront : frontier O ⊆ R.limit.function '' (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain))
    {a : ℝ} (ha : a ≤ 1)
    (hbound : ∀ z ∈ closure O,
      z ∈ R.limit.function '' (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain) →
      a < R.imageScalar i z) :
    ∀ᵐ z ∂volume, z ∈ closure O → a ≤ W.scalar z := by
  have hD := (R.limit.plane_open_embedding hG).2.1 _
    (hG.preimage OnePoint.continuous_coe) (Subset.refl _)
  have hc : ContinuousOn (fun z => 1 - R.imageScalar i z)
      (R.limit.function '' (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain)) :=
    continuousOn_const.sub (R.imageScalar_contDiffOn hG i).continuousOn
  obtain ⟨η, hη, hs, hu, hone, hd, hr⟩ := exists_range_preserving_cutoff hD hO hK hfront hc
    (b := 1 - a) (fun z hz hzi => sub_lt_sub_left (hbound z hz hzi) 1)
  let e := complexPlaneCoordinates
  have hdE (x : EuclideanPlane)
      (hx : e x ∉ R.limit.function '' (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain)) :
      fderiv ℝ (η ∘ e) x = 0 := by
    rw [fderiv_comp x (hη.differentiable (by simp) _) e.differentiableAt, hd _ hx]
    simp
  have hsource := complexPlaneCoordinates_measurePreserving.quasiMeasurePreserving.ae
    (W.eq_source_ae R hsch hG)
  have hcomp := localized_sobolev_range
    (aestronglyMeasurable_const.sub W.boundedRepresentative_measurable)
    (f := fun x => 1 - W.boundedRepresentative x)
    (G := fun x => -W.planarWeakGradient x)
    (fun x => ⟨sub_nonneg.mpr (W.boundedRepresentative_unit x).2,
      sub_le_self 1 (W.boundedRepresentative_unit x).1⟩)
    (fun j => (W.planarWeakGradient_memLp j).neg)
    (complement_weak_gradient W.boundedRepresentative_measurable W.boundedRepresentative_unit
      W.boundedRepresentative_weak)
    (D := e ⁻¹' (R.limit.function '' (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain)))
    (fun j => by
      filter_upwards [W.planarWeakGradient_zero_off_image hsch hG j] with x hx hout
      change -W.planarWeakGradient x j = 0
      rw [hx hout, neg_zero])
    (hη.comp e.contDiff) (hs.comp_homeomorph e.toHomeomorph) (fun x => hu (e x)) hdE
    (sub_nonneg.mpr ha) (by
      filter_upwards [hsource, W.boundedRepresentative_ae] with x hx hrep hxin hηx
      rw [hrep]
      change 1 - W.scalar (e x) ≤ 1 - a
      rw [hx hxin]
      exact hr (e x) hxin hηx)
  have hE : ∀ᵐ x ∂volume, (η ∘ e) x = 1 → a ≤ W.scalar (e x) := by
    filter_upwards [hcomp, W.boundedRepresentative_ae] with x hx hrep hηx
    have h := hx hηx
    rw [hrep] at h
    change 1 - W.scalar (e x) ≤ 1 - a at h
    linarith
  have hm := complexPlaneCoordinates_measurePreserving.symm e.toHomeomorph.toMeasurableEquiv
  filter_upwards [hm.quasiMeasurePreserving.ae hE] with z hz hzO
  have honez : η z = 1 := hone.self_of_nhdsSet z hzO
  change η (e (e.symm z)) = 1 → a ≤ W.scalar (e (e.symm z)) at hz
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using hz
    (by simpa only [ContinuousLinearEquiv.apply_symm_apply] using honez)

end ScalarWeakLimit
end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
