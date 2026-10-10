import OAI.Geometry.IsometricImmersion.Caps.CapReflectionCalculus
import OAI.Geometry.IsometricImmersion.Pulses.PulseProfiles
import OAI.Geometry.IsometricImmersion.Immersions.ActualShearHeight

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Flow.Reflection

theorem axisBump_even (a t : ℝ) : axisBump a (-t) = axisBump a t := by
  simp only [axisBump, neg_sq]

theorem inverseShear_reflect (q0 : ℝ) (p : Coord) :
    inverseShearCoordinates q0 (reflectPoint p) =
      reflectPoint (inverseShearCoordinates (-q0) p) := by
  ext i
  fin_cases i
  · change p 0 = p 0
    rfl
  · change -p 1-q0*p 0 = -(p 1-(-q0)*p 0)
    ring

theorem shear_reflect (q0 : ℝ) (p : Coord) :
    shearCoordinates q0 (reflectPoint p) =
      reflectPoint (shearCoordinates (-q0) p) := by
  ext i
  fin_cases i
  · change p 0 = p 0
    rfl
  · change -p 1+q0*p 0 = -(p 1+(-q0)*p 0)
    ring

theorem pulseScalar_reflect (a : ℝ) (N : ℕ) (delta tau : ℝ) (p : Coord) :
    pulseScalar a N delta tau (reflectPoint p) = pulseScalar a N delta tau p := by
  simp only [pulseScalar, reflectPoint_zero, reflectPoint_one, mul_neg, neg_div,
    temporalCutoff, axisBump_even]

theorem reflectedMetric_pulseTensor (q0 a : ℝ) (N : ℕ) (delta tau : ℝ) :
    reflectedMetric (pulseTensor q0 a N delta tau) = pulseTensor (-q0) a N delta tau := by
  funext p
  ext i j
  rw [reflectedMetric_entry]
  simp only [pulseTensor, shear_reflect, pulseScalar_reflect]
  fin_cases i <;> fin_cases j <;> simp [thetaCovector]

theorem reflectedMetric_testMetric (g : MetricField) (q0 a : ℝ) (N : ℕ)
    (delta tau : ℝ) :
    reflectedMetric (testMetric g q0 a N delta tau) =
      testMetric (reflectedMetric g) (-q0) a N delta tau := by
  rw [testMetric, reflectedMetric_add, reflectedMetric_pulseTensor]
  rfl

theorem reflectedMetric_sub (g h : MetricField) :
    reflectedMetric (g-h) = reflectedMetric g-reflectedMetric h := by
  funext p
  ext i j
  simp only [reflectedMetric_entry, Pi.sub_apply, Matrix.sub_apply]
  split_ifs <;> ring

theorem metric_shear_reflection (g : MetricField) (q0 : ℝ) :
    metricInShearCoordinates (reflectedMetric g) (-q0) =
      reflectedMetric (metricInShearCoordinates g q0) := by
  funext p
  ext i j
  simp only [metricInShearCoordinates, affinePullbackMetric,
    ← inverseShearCoordinates_eq_affine]
  rw [reflectedMetric_entry]
  simp only [affinePullbackMetric, ← inverseShearCoordinates_eq_affine,
    Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two,
    reflectedMetric_entry, inverseShear_reflect]
  fin_cases i <;> fin_cases j <;>
    simp [inverseShearMatrix] <;> ring

theorem height_shear_reflection (z : Coord → ℝ) (q0 : ℝ) :
    heightInShearCoordinates (reflectedScalar z) (-q0) =
      reflectedScalar (heightInShearCoordinates z q0) := by
  funext p
  change z (reflectPoint (inverseShearCoordinates (-q0) p)) =
    z (inverseShearCoordinates q0 (reflectPoint p))
  rw [inverseShear_reflect]

theorem reflected_pulse_approximation_jet_norm
    (gTau gStar : MetricField) (q0 a : ℝ) (N : ℕ) (delta tau : ℝ)
    (i j : Fin 2) (k : ℕ) (p : Coord) :
    ‖iteratedFDeriv ℝ k (fun q => reflectedMetric gTau q i j-
      testMetric (reflectedMetric gStar) (-q0) a N delta tau q i j) p‖ =
    ‖iteratedFDeriv ℝ k (fun q => gTau q i j-
      testMetric gStar q0 a N delta tau q i j) (reflectPoint p)‖ := by
  have hfun : (fun q => reflectedMetric gTau q i j-
      testMetric (reflectedMetric gStar) (-q0) a N delta tau q i j) =
      (fun q => reflectedMetric (gTau-testMetric gStar q0 a N delta tau) q i j) := by
    funext q
    simp only [← reflectedMetric_testMetric,reflectedMetric_sub,Pi.sub_apply,Matrix.sub_apply]
  rw [hfun]
  exact reflectedMetric_entry_jet_norm _ p i j k

end SmoothLocal.Pulse

end

end OAI
