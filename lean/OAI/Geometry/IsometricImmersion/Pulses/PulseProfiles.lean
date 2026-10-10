import OAI.Geometry.IsometricImmersion.Assembly.SupportedPerturbations
import OAI.Geometry.IsometricImmersion.Coordinates.AffinePullback
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise Distributions
open Set Filter

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Perturbation

def axisBump (a t : ℝ) : ℝ := expNegInvGlue (a ^ 2 - t ^ 2)

theorem axisBump_contDiff (a : ℝ) : ContDiff ℝ ∞ (axisBump a) :=
  expNegInvGlue.contDiff.comp (contDiff_const.sub (contDiff_id.pow 2))

theorem axisBump_nonneg (a t : ℝ) : 0 ≤ axisBump a t := expNegInvGlue.nonneg _

theorem axisBump_pos {a t : ℝ} (ha : 0 < a) (ht : |t| < a) : 0 < axisBump a t := by
  have hs : |t| ^ 2 < a ^ 2 := (sq_lt_sq₀ (abs_nonneg t) ha.le).mpr ht
  exact expNegInvGlue.pos_of_pos (sub_pos.mpr (by simpa only [sq_abs] using hs))

theorem axisBump_zero {a t : ℝ} (ha : 0 ≤ a) (ht : a ≤ |t|) : axisBump a t = 0 := by
  have hs : a ^ 2 ≤ |t| ^ 2 := (sq_le_sq₀ ha (abs_nonneg t)).mpr ht
  exact expNegInvGlue.zero_of_nonpos (sub_nonpos.mpr (by simpa only [sq_abs] using hs))

theorem axisBump_support_bound {a t : ℝ} (ha : 0 < a) (ht : axisBump a t ≠ 0) :
    |t| < a := by
  by_contra h
  exact ht (axisBump_zero ha.le (le_of_not_gt h))

theorem axisBump_tsupport_subset {a : ℝ} (ha : 0 < a) :
    tsupport (axisBump a) ⊆ Icc (-a) a := by
  apply closure_minimal _ isClosed_Icc
  intro t ht
  exact ⟨(abs_lt.mp (axisBump_support_bound ha ht)).1.le,
    (abs_lt.mp (axisBump_support_bound ha ht)).2.le⟩

theorem axisBump_hasCompactSupport {a : ℝ} (ha : 0 < a) : HasCompactSupport (axisBump a) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (axisBump_tsupport_subset ha)

theorem axisBump_pos_zero {a : ℝ} (ha : 0 < a) : 0 < axisBump a 0 :=
  axisBump_pos ha (by simpa using ha)

theorem axisBump_integral_pos {a : ℝ} (ha : 0 < a) : 0 < ∫ t : ℝ, axisBump a t :=
  (axisBump_contDiff a).continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (axisBump_hasCompactSupport ha) (axisBump_nonneg a) (axisBump_pos_zero ha).ne'

def spatialCutoff (L r : ℝ) : ℝ → ℝ := axisBump (L * r / 16)

def temporalCutoff : ℝ → ℝ := axisBump (1 / 2)

theorem temporalCutoff_integral_pos : 0 < ∫ t : ℝ, temporalCutoff t :=
  axisBump_integral_pos (by norm_num)

theorem spatialCutoff_tsupport_inside {L r : ℝ} (hL : 0 < L) (hr : 0 < r) :
    tsupport (spatialCutoff L r) ⊆ Ioo (-(L * r / 8)) (L * r / 8) := by
  intro t ht
  have h := axisBump_tsupport_subset (div_pos (mul_pos hL hr) (by norm_num)) ht
  constructor <;> nlinarith [mul_pos hL hr, h.1, h.2]

theorem temporalCutoff_tsupport_inside : tsupport temporalCutoff ⊆ Ioo (-1 : ℝ) 1 := by
  intro t ht
  have h := axisBump_tsupport_subset (by norm_num : (0 : ℝ) < 1 / 2) ht
  constructor <;> linarith [h.1, h.2]

def shearCoordinates (q0 : ℝ) (p : Coord) : Coord := ![p 0, p 1 + q0 * p 0]
def inverseShearCoordinates (q0 : ℝ) (p : Coord) : Coord := ![p 0, p 1 - q0 * p 0]
def inverseShearMatrix (q0 : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; -q0, 1]
def thetaCovector (q0 : ℝ) : Coord := ![q0, 1]

theorem shearCoordinates_contDiff (q0 : ℝ) : ContDiff ℝ ∞ (shearCoordinates q0) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · change ContDiff ℝ ∞ (fun x : Coord => x 0)
    fun_prop
  · change ContDiff ℝ ∞ (fun x : Coord => x 1 + q0 * x 0)
    fun_prop

theorem inverseShearCoordinates_contDiff (q0 : ℝ) : ContDiff ℝ ∞ (inverseShearCoordinates q0) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · change ContDiff ℝ ∞ (fun x : Coord => x 0)
    fun_prop
  · change ContDiff ℝ ∞ (fun x : Coord => x 1 - q0 * x 0)
    fun_prop

theorem shear_inverse (q0 : ℝ) (p : Coord) :
    shearCoordinates q0 (inverseShearCoordinates q0 p) = p := by
  ext i
  fin_cases i <;> simp [shearCoordinates, inverseShearCoordinates]

theorem inverse_shear (q0 : ℝ) (p : Coord) :
    inverseShearCoordinates q0 (shearCoordinates q0 p) = p := by
  ext i
  fin_cases i <;> simp [shearCoordinates, inverseShearCoordinates]

theorem inverseShearCoordinates_eq_affine (q0 : ℝ) :
    inverseShearCoordinates q0 = affineCoordinates 0 (inverseShearMatrix q0) := by
  ext p i
  fin_cases i <;> simp [inverseShearCoordinates, inverseShearMatrix,
    affineCoordinates, dotProduct, Fin.sum_univ_two]
  ring

def pulseScalar (a : ℝ) (N : ℕ) (delta tau : ℝ) (p : Coord) : ℝ :=
  (1 / tau ^ N) * axisBump a (p 0) * temporalCutoff (tau * p 1 / delta) *
    Real.cos (tau * p 0)

def pulseTensor (q0 a : ℝ) (N : ℕ) (delta tau : ℝ) : MetricField := fun p i j =>
  pulseScalar a N delta tau (shearCoordinates q0 p) * thetaCovector q0 i * thetaCovector q0 j

def testMetric (gStar : MetricField) (q0 a : ℝ) (N : ℕ) (delta tau : ℝ) : MetricField :=
  gStar + pulseTensor q0 a N delta tau

theorem pulseScalar_contDiff (a : ℝ) (N : ℕ) (delta tau : ℝ) :
    ContDiff ℝ ∞ (pulseScalar a N delta tau) := by
  unfold pulseScalar temporalCutoff
  exact ((contDiff_const.mul ((axisBump_contDiff a).comp (contDiff_apply ℝ ℝ 0))).mul
    ((axisBump_contDiff (1 / 2)).comp
      ((contDiff_const.mul (contDiff_apply ℝ ℝ 1)).div_const delta))).mul
    (Real.contDiff_cos.comp (contDiff_const.mul (contDiff_apply ℝ ℝ 0)))

theorem pulseTensor_contDiff (q0 a : ℝ) (N : ℕ) (delta tau : ℝ) :
    ContDiff ℝ ∞ (pulseTensor q0 a N delta tau) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  exact (((pulseScalar_contDiff a N delta tau).comp (shearCoordinates_contDiff q0)).mul
    contDiff_const).mul contDiff_const

theorem pulseTensor_symmetric (q0 a : ℝ) (N : ℕ) (delta tau : ℝ) (p : Coord) (i j : Fin 2) :
    pulseTensor q0 a N delta tau p i j = pulseTensor q0 a N delta tau p j i := by
  unfold pulseTensor
  ring

def pulseLocalBox (a delta tau : ℝ) : Set Coord :=
  Icc (![-a, -(delta / (2 * tau))]) (![a, delta / (2 * tau)])

def pulseOriginalBox (q0 a delta tau : ℝ) : Set Coord :=
  inverseShearCoordinates q0 '' pulseLocalBox a delta tau

theorem pulseLocalBox_isCompact (a delta tau : ℝ) : IsCompact (pulseLocalBox a delta tau) :=
  isCompact_Icc

theorem pulseOriginalBox_isCompact (q0 a delta tau : ℝ) :
    IsCompact (pulseOriginalBox q0 a delta tau) :=
  (pulseLocalBox_isCompact a delta tau).image (inverseShearCoordinates_contDiff q0).continuous

theorem pulseScalar_support_bound {a delta tau : ℝ} (ha : 0 < a)
    (hd : 0 < delta) (ht : 0 < tau) (N : ℕ) {p : Coord}
    (hp : pulseScalar a N delta tau p ≠ 0) : p ∈ pulseLocalBox a delta tau := by
  have hχ : axisBump a (p 0) ≠ 0 := by
    intro h
    apply hp
    simp only [pulseScalar, h, mul_zero, zero_mul]
  have hφ : temporalCutoff (tau * p 1 / delta) ≠ 0 := by
    intro h
    apply hp
    simp only [pulseScalar, h, mul_zero, zero_mul]
  have hx := abs_lt.mp (axisBump_support_bound ha hχ)
  have hy := axisBump_support_bound (by norm_num : (0 : ℝ) < 1 / 2) hφ
  have hy' : |p 1| < delta / (2 * tau) := by
    rw [abs_div, abs_mul, abs_of_pos ht, abs_of_pos hd] at hy
    apply (lt_div_iff₀ (mul_pos (by norm_num) ht)).mpr
    have hh := (div_lt_iff₀ hd).mp hy
    nlinarith
  constructor <;> intro i <;> fin_cases i
  · exact hx.1.le
  · exact (abs_lt.mp hy').1.le
  · exact hx.2.le
  · exact (abs_lt.mp hy').2.le

theorem pulseTensor_tsupport_subset {q0 a delta tau : ℝ}
    (ha : 0 < a) (hd : 0 < delta) (ht : 0 < tau) (N : ℕ) :
    tsupport (pulseTensor q0 a N delta tau) ⊆ pulseOriginalBox q0 a delta tau := by
  apply closure_minimal _ (pulseOriginalBox_isCompact q0 a delta tau).isClosed
  intro p hp
  have hs : pulseScalar a N delta tau (shearCoordinates q0 p) ≠ 0 := by
    intro h
    apply hp
    ext i j
    simp only [pulseTensor, h, zero_mul, Matrix.zero_apply]
  exact ⟨shearCoordinates q0 p, pulseScalar_support_bound ha hd ht N hs, inverse_shear q0 p⟩

theorem pulseTensor_hasCompactSupport {q0 a delta tau : ℝ}
    (ha : 0 < a) (hd : 0 < delta) (ht : 0 < tau) (N : ℕ) :
    HasCompactSupport (pulseTensor q0 a N delta tau) :=
  (pulseOriginalBox_isCompact q0 a delta tau).of_isClosed_subset (isClosed_tsupport _)
    (pulseTensor_tsupport_subset ha hd ht N)

theorem pulseOriginalBox_subset_patchBox {q0 a delta tau : ℝ}
    (ha : a ≤ 1 / 10) (hy : delta / (2 * tau) + |q0| * a ≤ 1 / 10) :
    pulseOriginalBox q0 a delta tau ⊆ patchBox := by
  rintro p ⟨u, hu, rfl⟩
  have hu0 : |u 0| ≤ a := abs_le.mpr ⟨hu.1 0, hu.2 0⟩
  have hu1 : |u 1| ≤ delta / (2 * tau) := abs_le.mpr ⟨hu.1 1, hu.2 1⟩
  have h0 : |inverseShearCoordinates q0 u 0| ≤ 1 / 10 := hu0.trans ha
  have h1 : |inverseShearCoordinates q0 u 1| ≤ 1 / 10 := by
    change |u 1 - q0 * u 0| ≤ _
    calc
      _ ≤ |u 1| + |q0 * u 0| := abs_sub _ _
      _ = |u 1| + |q0| * |u 0| := by rw [abs_mul]
      _ ≤ delta / (2 * tau) + |q0| * a :=
        add_le_add hu1 (mul_le_mul_of_nonneg_left hu0 (abs_nonneg q0))
      _ ≤ _ := hy
  constructor <;> intro i <;> fin_cases i
  · exact (abs_le.mp h0).1
  · exact (abs_le.mp h1).1
  · exact (abs_le.mp h0).2
  · exact (abs_le.mp h1).2

def supportedPulse (q0 a : ℝ) (N : ℕ) (delta tau : ℝ)
    (ha : 0 < a) (hd : 0 < delta) (ht : 0 < tau)
    (hax : a ≤ 1 / 10) (hay : delta / (2 * tau) + |q0| * a ≤ 1 / 10) :
    SymmetricPerturbation := by
  let f : SupportedTensor := ⟨pulseTensor q0 a N delta tau,
    pulseTensor_contDiff q0 a N delta tau, by
      intro p hp
      apply image_eq_zero_of_notMem_tsupport
      exact fun h => hp (pulseOriginalBox_subset_patchBox hax hay
        (pulseTensor_tsupport_subset ha hd ht N h))⟩
  exact ⟨f, pulseTensor_symmetric q0 a N delta tau⟩

theorem pulseTensor_inverseShear (q0 a : ℝ) (N : ℕ) (delta tau : ℝ) (p : Coord) :
    affinePullbackMetric (pulseTensor q0 a N delta tau) 0 (inverseShearMatrix q0) p =
      !![0, 0; 0, pulseScalar a N delta tau p] := by
  rw [affinePullbackMetric, ← inverseShearCoordinates_eq_affine]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pulseTensor, shear_inverse, inverseShearMatrix, thetaCovector,
      Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem testMetric_inverseShear (gStar : MetricField) (q0 a : ℝ) (N : ℕ)
    (delta tau : ℝ) (p : Coord) :
    affinePullbackMetric (testMetric gStar q0 a N delta tau) 0 (inverseShearMatrix q0) p =
      affinePullbackMetric gStar 0 (inverseShearMatrix q0) p +
        !![0, 0; 0, pulseScalar a N delta tau p] := by
  rw [← pulseTensor_inverseShear q0 a N delta tau p]
  simp only [affinePullbackMetric, testMetric, Pi.add_apply, mul_add, add_mul]

end SmoothLocal.Pulse

end

end OAI
