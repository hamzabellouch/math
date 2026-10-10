import OAI.Probability.InvariantIsing.Magnetic.MagneticWassersteinMain
import Mathlib.MeasureTheory.Measure.Prod

namespace OAI

/-! The joint conditional-Haar hypothesis for random spectra and fields.
Only the one-dimensional marginal orbit law is prescribed at each dimension. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace InvariantIsing

abbrev FieldSpectralData (N : ℕ) := (Fin N → ℝ) × (Fin N → ℝ)

def dataPhysicalPressure {N : ℕ} (d : FieldSpectralData N) (U : Orthogonal N) : ℝ :=
  rotatedPressure d.1 (matrixRotation U⁻¹) d.2

lemma measurable_random_specialPressure {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (eig field : Ω → Fin N → ℝ) (heig : Measurable eig) (hfield : Measurable field)
    (U : Ω → SpecialOrthogonal N) (hU : Measurable U) :
    Measurable (fun ω => rotatedPressure (eig ω) (specialRotation (U ω)) (field ω)) := by
  have hE (σ : Spin N) : Measurable (fun ω =>
      rotatedEnergy (eig ω) (specialRotation (U ω)) σ+fieldEnergy (field ω) σ) := by
    apply Measurable.add
    · exact ((Finset.measurable_sum _ fun i _ =>
        ((measurable_pi_apply i).comp heig).mul
          (((measurable_specialRotation_eval (spinVector σ) i).comp hU).pow_const 2))).const_mul (1/2 : ℝ)
    · exact Finset.measurable_sum _ fun i _ => ((measurable_pi_apply i).comp hfield).mul_const _
  unfold rotatedPressure logPartition
  exact ((Finset.measurable_sum _ fun σ _ => (hE σ).exp).const_mul
    (Fintype.card (Spin N) : ℝ)⁻¹).log.const_mul (N : ℝ)⁻¹

lemma measurable_dataPhysicalPressure {N : ℕ} (hN : 0 < N) :
    Measurable (fun z : FieldSpectralData N × Orthogonal N => dataPhysicalPressure z.1 z.2) := by
  have hh := measurable_random_specialPressure
    (fun z : FieldSpectralData N × Orthogonal N => z.1.1)
    (fun z : FieldSpectralData N × Orthogonal N => z.1.2)
    (measurable_fst.comp measurable_fst) (measurable_snd.comp measurable_fst)
    (fun z => cavityOrientationLift hN z.2⁻¹)
    ((measurable_cavityOrientationLift hN).comp measurable_snd.inv)
  convert hh using 1
  funext z
  simp only [dataPhysicalPressure,rotatedPressure,cavityOrientationLift_energy]

lemma measurable_dataPressureMean {N : ℕ} (hN : 0 < N)
    (H : Measure (Orthogonal N)) [SFinite H] :
    Measurable (fun d : FieldSpectralData N => ∫ U, dataPhysicalPressure d U ∂H) :=
  (measurable_dataPhysicalPressure hN).stronglyMeasurable.integral_prod_right'.measurable

/-- Conditional jointly on the spectrum and field, the pressure has its Haar orbit law.
This formulation allows arbitrary dependence across dimensions and between the two data sets. -/
def ConditionalFieldOrbitLaw {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (P : Measure Ω) (d : Ω → FieldSpectralData N) (pressure : Ω → ℝ)
    (H : Measure (Orthogonal N)) : Prop :=
  P.map (fun ω => (d ω,pressure ω))=
    ((P.map d).prod H).map (fun z => (z.1,dataPhysicalPressure z.1 z.2))

end InvariantIsing

end

end OAI
