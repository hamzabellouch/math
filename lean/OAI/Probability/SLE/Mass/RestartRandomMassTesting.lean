import OAI.Probability.SLE.Mass.RadonRandomTesting
import OAI.Probability.SLE.Geometry.RandomRestartEvents

namespace OAI

/-! The fresh-driver law may be tested against a random spatial weight
measurable in the stopped past. This is the conditional-Tonelli step for
the restart candidate, before invoking uniqueness. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped ENNReal

namespace SLEExactGauge

lemma fresh_mass_test_joint_measurable
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (M : X → Measure upperHalfPlane) (hM : Measurable M)
    (hMf : ∀ x, IsFiniteMeasureOnCompacts (M x))
    (f : Ω × upperHalfPlane → ℝ≥0∞) (hf : Measurable f) :
    Measurable (fun p : Ω × X => ∫⁻ z, f (p.1,z) ∂M p.2) := by
  exact halfPlane_random_test_measurable (fun p : Ω × X => M p.2)
    (hM.comp measurable_snd) (fun p => hMf p.2)
    (fun p : (Ω × X) × upperHalfPlane => f (p.1.1,p.2))
    (hf.comp (measurable_fst.fst.prodMk measurable_snd))

theorem restart_random_mass_test
    {Ω X : Type*} [mΩ : MeasurableSpace Ω] [mX : MeasurableSpace X]
    (P : Measure Ω) [IsFiniteMeasure P] (ν : Measure X) [IsFiniteMeasure ν]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (Y : Ω → X) (hY : Measurable[mΩ] Y)
    (hlaw : ∀ A : Set Ω, MeasurableSet[m] A →
      @Measure.map Ω X mΩ mX Y (P.restrict A) = P A • ν)
    (M : X → Measure upperHalfPlane) (hM : Measurable M)
    (hMf : ∀ x, IsFiniteMeasureOnCompacts (M x))
    (f : Ω × upperHalfPlane → ℝ≥0∞)
    (hf : Measurable[m.prod inferInstance] f) :
    (∫⁻ ω, ∫⁻ z, f (ω,z) ∂M (Y ω) ∂P) =
      ∫⁻ ω, ∫⁻ z, f (ω,z) ∂ν.bind M ∂P := by
  let : MeasurableSpace Ω := mΩ
  have hg : Measurable[m.prod mX]
      (fun p : Ω × X => ∫⁻ z, f (p.1,z) ∂M p.2) :=
    @fresh_mass_test_joint_measurable Ω X m mX M hM hMf f hf
  rw [@restart_lintegral_random_test Ω X mΩ mX P inferInstance ν inferInstance
    m hm Y hY hlaw _ hg]
  apply lintegral_congr
  intro ω
  exact (Measure.lintegral_bind hM.aemeasurable
    (hf.comp (measurable_const.prodMk measurable_id)).aemeasurable).symm

end SLEExactGauge

end

end OAI
