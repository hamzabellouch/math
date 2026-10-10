import Mathlib
import OAI.Geometry.CAT0Fillings.Charts.Differentiability

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace CAT0Fillings
open MeasureTheory Set Filter
open scoped Topology NNReal

namespace IntegerChart
variable {X : Type*} [MetricSpace X]
variable {k : ℕ} (C : IntegerChart X k)
lemma scalar_eq {f : X → ℝ} {z : Euc k} (hz : z ∈ C.domain) :
    C.scalar f z = f (C.param ⟨z, hz⟩) := by simp [scalar, hz]

lemma scalar_mul (f g : X → ℝ) :
    C.scalar (fun x => f x * g x) = C.scalar f * C.scalar g := by
  funext z
  by_cases hz : z ∈ C.domain
  · simp [scalar, hz]
  · simp [scalar, hz]

lemma scalar_lipschitzOn {f : X → ℝ} {K L : ℝ≥0}
    (hφ : LipschitzWith L C.param) (hf : LipschitzWith K f) :
    LipschitzOnWith (K * L) (C.scalar f) C.domain := by
  apply lipschitzOnWith_iff_restrict.mpr
  convert hf.comp hφ using 1
  funext z
  exact C.scalar_eq z.property

lemma measurable_scalar {f : X → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    Measurable (C.scalar f) := by
  obtain ⟨L, U, hφ, _⟩ := C.bilipschitz
  obtain ⟨F, hF, heq⟩ := (C.scalar_lipschitzOn hφ hf).extend_real
  have hsc : C.scalar f = C.domain.indicator F := by
    funext z
    by_cases hz : z ∈ C.domain
    · simpa [hz] using heq hz
    · simp [scalar, hz]
  rw [hsc]
  exact hF.continuous.measurable.indicator C.borel

lemma ae_differentiableWithinAt_scalar {f : X → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) :
    ∀ᵐ z ∂volume.restrict C.domain, DifferentiableWithinAt ℝ (C.scalar f) C.domain z := by
  obtain ⟨L, U, hφ, _⟩ := C.bilipschitz
  obtain ⟨F, hF, heq⟩ := (C.scalar_lipschitzOn hφ hf).extend_real
  filter_upwards [ae_restrict_mem C.borel,
    (hF.ae_differentiableAt (μ := volume)).filter_mono (ae_mono Measure.restrict_le_self)]
    with z hz hd
  exact hd.differentiableWithinAt.congr heq (heq hz)

lemma ae_fderivWithin_scalar_mul {f g : X → ℝ} {K J : ℝ≥0}
    (hf : LipschitzWith K f) (hg : LipschitzWith J g) :
    ∀ᵐ z ∂volume.restrict C.domain,
      fderivWithin ℝ (C.scalar (fun x => f x * g x)) C.domain z =
        C.scalar f z • fderivWithin ℝ (C.scalar g) C.domain z +
        C.scalar g z • fderivWithin ℝ (C.scalar f) C.domain z := by
  filter_upwards [ae_uniqueDiffWithinAt volume C.domain,
    C.ae_differentiableWithinAt_scalar hf, C.ae_differentiableWithinAt_scalar hg]
    with z hz hdf hdg
  rw [C.scalar_mul]
  exact fderivWithin_mul hz hdf hdg

lemma ae_jacobian_eq_extensions {π : Fin k → X → ℝ} {F : Fin k → Euc k → ℝ}
    {L : Fin k → ℝ≥0} (hF : ∀ i, LipschitzWith (L i) (F i))
    (heq : ∀ i, EqOn (C.scalar (π i)) (F i) C.domain) :
    C.jacobian π =ᵐ[volume.restrict C.domain]
      fun z => Matrix.det (Matrix.of fun i j => fderiv ℝ (F i) z (EuclideanSpace.single j 1)) := by
  have hae : ∀ᵐ z ∂volume.restrict C.domain, ∀ i,
      fderivWithin ℝ (C.scalar (π i)) C.domain z = fderiv ℝ (F i) z :=
    ae_all_iff.mpr fun i => ae_fderivWithin_eq_fderiv_extension volume C.borel (hF i) (heq i)
  filter_upwards [hae] with z hz
  simp only [jacobian, hz]
  rfl

lemma jacobian_aestronglyMeasurable {π : Fin k → X → ℝ}
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    AEStronglyMeasurable (C.jacobian π) (volume.restrict C.domain) := by
  obtain ⟨L, U, hφ, _⟩ := C.bilipschitz
  choose K hK using hπ
  choose F hF heq using fun i => (C.scalar_lipschitzOn hφ (hK i)).extend_real
  have hmeas : Measurable (fun z => Matrix.det
      (Matrix.of fun i j => fderiv ℝ (F i) z (EuclideanSpace.single j 1))) := by
    simp only [Matrix.det_apply']
    fun_prop
  exact hmeas.aestronglyMeasurable.congr (C.ae_jacobian_eq_extensions hF heq).symm

end IntegerChart
end CAT0Fillings
end

end OAI
