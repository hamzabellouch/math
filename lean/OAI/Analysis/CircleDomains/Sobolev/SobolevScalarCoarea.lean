import OAI.Analysis.CircleDomains.Sobolev.LocalComplexWitness
import Mathlib.MeasureTheory.Measure.Hausdorff

namespace OAI

/-!
The scalar planar specialization of Malý–Swanson–Ziemer,
*The co-area formula for Sobolev mappings*, Trans. AMS 355 (2003),
477–492, Theorem 1.1, DOI 10.1090/S0002-9947-02-03091-X.
Primary author text: https://arxiv.org/pdf/math/0112008, Theorem 1.1
and (1.2), p.1; nonnegative weights follow by the simple-function
approximation described before (1.2). The precise representative is
automatic for a continuous function, by the definition (2.5), p.5.

Only continuous real W1,2_loc functions on the plane and bounded Borel
sets are used. The derivative is the actual distributional gradient.
The proposition below contains no level topology or null image assertion.
-/
open Set Function Filter MeasureTheory Bornology
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 def sobolevLevelIntegral (E : Set EuclideanPlane) (v : EuclideanPlane → ℝ)
    (q : EuclideanPlane → ℝ≥0∞) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ p in E ∩ {p | v p = t}, q p ∂(μH[1] : Measure EuclideanPlane)

 def PlanarSobolevCoarea : Prop :=
  ∀ (v : EuclideanPlane → ℝ), Continuous v →
  ∀ (V : EuclideanPlane → EuclideanPlane), DeGiorgi.HasWeakGrad V v univ →
  (∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (Metric.ball 0 R))) →
  ∀ (E : Set EuclideanPlane), MeasurableSet E → IsBounded E →
  ∀ (q : EuclideanPlane → ℝ≥0∞), Measurable q →
    AEMeasurable (sobolevLevelIntegral E v q) volume ∧
    (∫⁻ t, sobolevLevelIntegral E v q t) =
      ∫⁻ p in E, q p * ENNReal.ofReal ‖V p‖

 theorem sobolev_level_integral_zero_of_gradient_zero
    (hcoarea : PlanarSobolevCoarea)
    {v : EuclideanPlane → ℝ} (hv : Continuous v)
    {V : EuclideanPlane → EuclideanPlane} (hw : DeGiorgi.HasWeakGrad V v univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (Metric.ball 0 R)))
    {E : Set EuclideanPlane} (hE : MeasurableSet E) (hb : IsBounded E)
    (hz : ∀ᵐ p ∂volume.restrict E, V p = 0)
    {q : EuclideanPlane → ℝ≥0∞} (hq : Measurable q) :
    ∀ᵐ t ∂volume, sobolevLevelIntegral E v q t = 0 := by
  obtain ⟨hm, he⟩ := hcoarea v hv V hw hLp E hE hb q hq
  have hr : (∫⁻ p in E, q p * ENNReal.ofReal ‖V p‖) = 0 := by
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [hz] with p hp
    simp only [hp, norm_zero, ENNReal.ofReal_zero, mul_zero, Pi.zero_apply]
  rw [hr] at he
  exact (lintegral_eq_zero_iff' hm).mp he

end CircleDomainRigidity

end

end OAI
