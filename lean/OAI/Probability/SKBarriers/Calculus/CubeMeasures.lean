import Mathlib
import OAI.Probability.SKBarriers.Calculus.ParameterCalculus

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
namespace SK.Analytic

instance parameterMeasurable : (n : ℕ) → MeasurableSpace (ParameterSpace n)
  | 0 => inferInstanceAs (MeasurableSpace ℝ)
  | n+1 => letI := parameterMeasurable n; inferInstanceAs (MeasurableSpace (ParameterSpace n × ℝ))

instance parameterBorel : (n : ℕ) → BorelSpace (ParameterSpace n)
  | 0 => inferInstanceAs (BorelSpace ℝ)
  | n+1 => letI := parameterBorel n; inferInstanceAs (BorelSpace (ParameterSpace n × ℝ))

instance parameterSecondCountable : (n : ℕ) → SecondCountableTopology (ParameterSpace n)
  | 0 => inferInstanceAs (SecondCountableTopology ℝ)
  | n+1 => letI := parameterSecondCountable n; inferInstanceAs (SecondCountableTopology (ParameterSpace n × ℝ))

def fiberMeasure : (n : ℕ) → ℝ → Measure (ParameterSpace n)
  | 0, x => Measure.dirac x
  | n+1, x => (fiberMeasure n x).prod volume

instance fiberSigmaFinite : (n : ℕ) → (x : ℝ) → SigmaFinite (fiberMeasure n x)
  | 0, x => inferInstanceAs (SigmaFinite (Measure.dirac x))
  | n+1, x => letI := fiberSigmaFinite n x; inferInstanceAs (SigmaFinite ((fiberMeasure n x).prod volume))

def cubeMeasure : (n : ℕ) → ℝ → ℝ → ℝ → Measure (ParameterSpace n)
  | 0, x, _, _ => Measure.dirac x
  | n+1, x, a, b => (cubeMeasure n x a b).prod (volume.restrict (Ioc a b))

instance cubeFiniteMeasure : (n : ℕ) → (x a b : ℝ) → IsFiniteMeasure (cubeMeasure n x a b)
  | 0, x, _, _ => inferInstanceAs (IsFiniteMeasure (Measure.dirac x))
  | n+1, x, a, b => letI := cubeFiniteMeasure n x a b
                    inferInstanceAs (IsFiniteMeasure ((cubeMeasure n x a b).prod (volume.restrict (Ioc a b))))

def cubeSupport : (n : ℕ) → ℝ → ℝ → ℝ → Set (ParameterSpace n)
  | 0, x, _, _ => {x}
  | n+1, x, a, b => (cubeSupport n x a b) ×ˢ Icc a b

theorem cubeSupport_compact (n : ℕ) (x a b : ℝ) : IsCompact (cubeSupport n x a b) := by
  induction n with
  | zero => exact isCompact_singleton
  | succ n ih => exact ih.prod isCompact_Icc

theorem ae_mem_cubeSupport (n : ℕ) (x a b : ℝ) :
    ∀ᵐ z ∂cubeMeasure n x a b, z ∈ cubeSupport n x a b := by
  induction n with
  | zero => simp [cubeMeasure, cubeSupport]
  | succ n ih =>
    apply (Measure.ae_prod_mem_iff_ae_ae_mem (cubeSupport_compact (n+1) x a b).measurableSet).mpr
    filter_upwards [ih] with z hz
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    exact ⟨hz, ⟨hy.1.le, hy.2⟩⟩

theorem integrable_cubeMeasure (n : ℕ) (f : ParameterSpace n → ℝ)
    (hf : Continuous f) (x a b : ℝ) : Integrable f (cubeMeasure n x a b) := by
  obtain ⟨C, hC⟩ := (cubeSupport_compact n x a b).exists_bound_of_continuousOn hf.continuousOn
  apply (integrable_const C).mono' hf.aestronglyMeasurable
  filter_upwards [ae_mem_cubeSupport n x a b] with z hz
  exact hC z hz

theorem cubeIntegral_eq_measureIntegral (n : ℕ) (f : ParameterSpace n → ℝ)
    (hf : Continuous f) {a b : ℝ} (hab : a ≤ b) (x : ℝ) :
    cubeIntegral n f a b x = ∫ z, f z ∂cubeMeasure n x a b := by
  induction n with
  | zero => exact (integral_dirac _ _).symm
  | succ n ih =>
    change cubeIntegral n (fun z => ∫ y in a..b, f (z,y)) a b x =
      ∫ z, f z ∂(cubeMeasure n x a b).prod (volume.restrict (Ioc a b))
    rw [integral_prod f (integrable_cubeMeasure (n+1) f hf x a b)]
    rw [ih _ (contDiff_zero.mp (contDiff_intervalIntegral 0 f (contDiff_zero.mpr hf) a b))]
    apply integral_congr_ae
    exact ae_of_all _ (fun z => intervalIntegral.integral_of_le hab)

def cubeSet : (n : ℕ) → ℝ → ℝ → Set (ParameterSpace n)
  | 0, _, _ => univ
  | n+1, a, b => cubeSet n a b ×ˢ Ioc a b

theorem cubeSet_measurable (n : ℕ) (a b : ℝ) : MeasurableSet (cubeSet n a b) := by
  induction n with
  | zero => exact MeasurableSet.univ
  | succ n ih => exact ih.prod measurableSet_Ioc

theorem cubeMeasure_eq_restrict (n : ℕ) (x a b : ℝ) :
    cubeMeasure n x a b = (fiberMeasure n x).restrict (cubeSet n a b) := by
  induction n with
  | zero => simp [cubeMeasure, fiberMeasure, cubeSet]
  | succ n ih =>
    change (cubeMeasure n x a b).prod (volume.restrict (Ioc a b)) = _
    rw [ih, Measure.prod_restrict]
    rfl

end SK.Analytic

end
end
end
end
end

end OAI
