import OAI.Analysis.CircleDomains.Sobolev.ScalarEnergySaturation
import OAI.Analysis.CircleDomains.Sobolev.ScalarSobolevLimit

namespace OAI

/-! A pointwise unit-bounded representative of the actual weak scalar,
with the same global planar weak gradient. -/
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

 def boundedRepresentative (x : EuclideanPlane) : ℝ :=
  clipScalar (W.scalar (complexPlaneCoordinates x))

 def planarWeakGradient (x : EuclideanPlane) : EuclideanPlane :=
  WithLp.toLp 2 (fun j => if j = 0 then W.horizontal (complexPlaneCoordinates x)
    else W.vertical (complexPlaneCoordinates x))

 theorem boundedRepresentative_unit (x : EuclideanPlane) :
    W.boundedRepresentative x ∈ Icc 0 1 := clipScalar_mem _

 theorem boundedRepresentative_ae : W.boundedRepresentative =ᵐ[volume]
    W.scalar ∘ complexPlaneCoordinates := by
  filter_upwards [complexPlaneCoordinates_measurePreserving.quasiMeasurePreserving.ae W.scalar_unit]
    with x hx
  exact clipScalar_eq hx

 theorem boundedRepresentative_measurable : AEStronglyMeasurable W.boundedRepresentative volume :=
  clipScalar_lipschitz.continuous.comp_aestronglyMeasurable
    (W.scalar_aestronglyMeasurable.comp_quasiMeasurePreserving
      complexPlaneCoordinates_measurePreserving.quasiMeasurePreserving)

 theorem planarWeakGradient_memLp (j : Fin 2) :
    MemLp (fun x => W.planarWeakGradient x j) 2 volume := by
  fin_cases j
  · change MemLp (W.horizontal ∘ complexPlaneCoordinates) 2 volume
    exact (Lp.memLp W.horizontal).comp_measurePreserving complexPlaneCoordinates_measurePreserving
  · change MemLp (W.vertical ∘ complexPlaneCoordinates) 2 volume
    exact (Lp.memLp W.vertical).comp_measurePreserving complexPlaneCoordinates_measurePreserving

 theorem boundedRepresentative_weak :
    DeGiorgi.HasWeakGrad W.planarWeakGradient W.boundedRepresentative univ := by
  have hsame (j : Fin 2) (g : EuclideanPlane → ℝ)
      (hw : DeGiorgi.HasWeakPartialDeriv j g (W.scalar ∘ complexPlaneCoordinates) univ) :
      DeGiorgi.HasWeakPartialDeriv j g W.boundedRepresentative univ := by
    intro φ hφ hs hsub
    have ht := hw φ hφ hs hsub
    simp only [Measure.restrict_univ] at ht ⊢
    rw [← ht]
    apply integral_congr_ae
    filter_upwards [W.boundedRepresentative_ae] with x hx
    rw [hx]
  intro j
  fin_cases j
  · change DeGiorgi.HasWeakPartialDeriv 0 (W.horizontal ∘ complexPlaneCoordinates)
      W.boundedRepresentative univ
    apply hsame
    simpa only [preimage_univ] using weakPartial_of_complex_identity 0 1 complexPlaneCoordinates_zero
      (fun φ hφ hs => (W.derivative φ hφ hs).1) univ
  · change DeGiorgi.HasWeakPartialDeriv 1 (W.vertical ∘ complexPlaneCoordinates)
      W.boundedRepresentative univ
    apply hsame
    simpa only [preimage_univ] using weakPartial_of_complex_identity 1 Complex.I complexPlaneCoordinates_one
      (fun φ hφ hs => (W.derivative φ hφ hs).2) univ

 theorem planarWeakGradient_zero_off_image (hsch : PlanarSchoenflies)
    (hG : IsOpen d.physicalDomain) (j : Fin 2) :
    ∀ᵐ x ∂volume, complexPlaneCoordinates x ∉
      R.limit.function '' (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain) →
        W.planarWeakGradient x j = 0 := by
  filter_upwards [complexPlaneCoordinates_measurePreserving.quasiMeasurePreserving.ae
    (W.zero_gradient_off_image hsch hG)] with x hx hout
  fin_cases j
  · exact (hx hout).1
  · exact (hx hout).2

end ScalarWeakLimit
end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
