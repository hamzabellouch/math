import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.BalancedActivation
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.BalancedPlanarOrbit

namespace OAI

/-! One compact Hamiltonian translation loads the input point. The source
and target belong to a fixed rectangle, hence its whole straight path is
inside the cutoff plateau and outside the balanced cube after stretching. -/

noncomputable section
namespace ForcedComputation.BalancedLoader
open ShearFlows PlanarHamiltonian Set
open scoped ContDiff

def start : Plane := ![4, 0]
def rectangle : RationalBox 2 := ⟨![0, -1], ![4, 1]⟩
def direction (q : Plane) : Plane := q - start

def potential (q : Plane) (x : Plane) : ℝ :=
  rectangleCutoff rectangle 1 x * translationPotential (direction q) x

def spatial (q : Plane) : Plane → Plane := field (potential q)
def clock : ℝ → ℝ := smoothRamp (1 / 8) (1 / 4)
def pulse : ℝ → ℝ := smoothPulse (1 / 8) (1 / 4)
def planarVelocity (q : Plane) (t : ℝ) (x : Plane) : Plane := pulse t • spatial q x

def planarPath (q : Plane) (t : ℝ) : Plane := start + clock t • direction q

def raw (q : Plane) : Velocity := CompactLift.velocity BalancedBody.verticalCutoff (planarVelocity q)
def velocity (q : Plane) : Velocity := BalancedStretch.velocity (raw q)
def path (q : Plane) (t : ℝ) : Space := BalancedStretch.stretch (atHeight (planarPath q t) 0)

theorem spatial_smooth (q : Plane) : ContDiff ℝ ∞ (spatial q) :=
  field_smooth ((rectangleCutoff_smooth rectangle 1).mul (translationPotential_smooth _))

theorem planarVelocity_smooth (q : Plane) :
    ContDiff ℝ ∞ (fun y : ℝ × Plane => planarVelocity q y.1 y.2) :=
  ((smoothPulse_smooth _ _).comp contDiff_fst).smul ((spatial_smooth q).comp contDiff_snd)

theorem velocity_smooth (q : Plane) : ContDiff ℝ ∞ (velocity q) :=
  BalancedStretch.velocity_smooth
    (CompactLift.velocity_smooth BalancedBody.verticalCutoff_smooth (planarVelocity_smooth q))

theorem planarPath_in_rectangle {q : Plane} (hq : ∀ j, 0 ≤ q j ∧ q j ≤ 1) (t : ℝ) :
    planarPath q t ∈ rectangle.carrier := by
  have hc := smoothRamp_range (1 / 8) (1 / 4) t
  obtain ⟨hc0, hc1⟩ := hc
  intro j
  fin_cases j
  · norm_num [rectangle, planarPath, direction, start, Matrix.vecHead, Matrix.vecTail]
    dsimp only [clock] at *
    constructor
    · nlinarith [mul_nonneg hc0 (hq 0).1]
    · have hp := mul_nonpos_of_nonneg_of_nonpos hc0
        (show q 0 - 4 ≤ 0 by linarith [(hq 0).2])
      nlinarith
  · norm_num [rectangle, planarPath, direction, start, Matrix.vecHead, Matrix.vecTail]
    dsimp only [clock] at *
    constructor
    · nlinarith [mul_nonneg hc0 (hq 1).1]
    · nlinarith [mul_le_mul hc1 (hq 1).2 (hq 1).1 (by norm_num : (0 : ℝ) ≤ 1)]

theorem spatial_on_rectangle (q : Plane) {x : Plane} (hx : x ∈ rectangle.carrier) :
    spatial q x = direction q := by
  change field (fun y => rectangleCutoff rectangle 1 y * translationPotential (direction q) y) x = _
  rw [field_cutoff_plateau _ _
    (rectangleCutoff_one_near (by norm_num : (0 : ℚ) < 1) hx), field_translation]

theorem planarPath_deriv {q : Plane} (hq : ∀ j, 0 ≤ q j ∧ q j ≤ 1) (t : ℝ) :
    HasDerivAt (planarPath q) (planarVelocity q t (planarPath q t)) t := by
  have hθ : HasDerivAt clock (pulse t) t :=
    ((smoothRamp_smooth (1 / 8) (1 / 4)).differentiable (by simp) t).hasDerivAt
  have hd := (hθ.smul_const (direction q)).const_add start
  have he : planarVelocity q t (planarPath q t) = pulse t • direction q := by
    rw [planarVelocity, spatial_on_rectangle q (planarPath_in_rectangle hq t)]
  rw [he]
  exact hd

theorem path_deriv {q : Plane} (hq : ∀ j, 0 ≤ q j ∧ q j ≤ 1) (t : ℝ) :
    HasDerivAt (path q) (velocity q (t, path q t)) t := by
  have h := CompactLift.trajectory_atHeight (V := planarVelocity q) (a := 0)
    BalancedBody.verticalCutoff_zero (by simpa only [zero_add] using planarPath_deriv hq t)
  apply hasDerivAt_pi.mpr
  intro j
  simpa only [zero_add, path, velocity, raw] using
    (hasDerivAt_pi.mp (BalancedStretch.trajectory h)) j

theorem path_before (q : Plane) {t : ℝ} (ht : t ≤ 1 / 8) :
    path q t = ![4, 0, 0] := by
  have hc : clock t = 0 := smoothRamp_before (by norm_num) ht
  ext j
  fin_cases j <;> simp [path, planarPath, hc, start, BalancedStretch.coefficient, atHeight]

theorem path_after (q : Plane) {t : ℝ} (ht : 1 / 4 ≤ t) :
    path q t = BalancedStretch.stretch (atHeight q 0) := by
  have hc : clock t = 1 := smoothRamp_after (by norm_num) ht
  rw [path, planarPath, hc, one_smul, direction]
  congr 2
  abel

theorem path_safe {q : Plane} (hq : 4 ≤ q 0 + 16 * q 1) (t : ℝ) :
    path q t ∉ BalancedStretch.observer := by
  have hc := smoothRamp_range (1 / 8) (1 / 4) t
  have he : path q t = (1 - clock t) • ![4, 0, 0] +
      clock t • BalancedStretch.stretch (atHeight q 0) := by
    ext j
    fin_cases j <;> simp [path, planarPath, direction, start, atHeight,
      BalancedStretch.coefficient, Matrix.vecHead, Matrix.vecTail] <;> ring
  rw [he]
  apply BalancedStretch.loading_outside
  · simpa [BalancedStretch.coefficient, atHeight] using hq
  · exact hc

theorem velocity_before (q : Plane) {t : ℝ} (ht : t ≤ 1 / 8) (x : Space) :
    velocity q (t, x) = 0 := by
  have hp : pulse t = 0 := smoothPulse_before (by norm_num) ht
  simp [velocity, BalancedStretch.velocity, BalancedStretch.push, raw, CompactLift.velocity,
    CompactLift.spatial, VelocityDetector.triangularLift, planarVelocity, hp]

theorem velocity_after (q : Plane) {t : ℝ} (ht : 1 / 4 ≤ t) (x : Space) :
    velocity q (t, x) = 0 := by
  have hp : pulse t = 0 := smoothPulse_after (by norm_num) ht
  simp [velocity, BalancedStretch.velocity, BalancedStretch.push, raw, CompactLift.velocity,
    CompactLift.spatial, VelocityDetector.triangularLift, planarVelocity, hp]


def rawSupport : Set Space := Icc ![-2, -3, -2] ![6, 3, 2]
def support : Set Space := BalancedStretch.stretch '' rawSupport

theorem support_compact : IsCompact support :=
  (isCompact_Icc : IsCompact rawSupport).image BalancedStretch.stretch.continuous

theorem spatial_support (q : Plane) :
    tsupport (spatial q) ⊆ (rectangleCollar rectangle 1).carrier :=
  (field_tsupport (potential q)).trans
    (tsupport_mul_subset_left.trans (closure_minimal
      (rectangleCutoff_support (by norm_num : (0 : ℚ) < 1))
      (rectangleCollar_compact rectangle 1).isClosed))

theorem raw_support (q : Plane) (t : ℝ) :
    tsupport (fun x => raw q (t, x)) ⊆ rawSupport := by
  apply closure_minimal _ (isCompact_Icc : IsCompact rawSupport).isClosed
  intro x hx
  have hχ : BalancedBody.verticalCutoff (x 2) ≠ 0 := by
    intro hz
    apply hx
    simp only [raw, CompactLift.velocity, CompactLift.spatial, hz, zero_smul]
  have hV : spatial q (horizontal x) ≠ 0 := by
    intro hz
    apply hx
    simp only [raw, CompactLift.velocity, CompactLift.spatial, VelocityDetector.triangularLift,
      VelocityDetector.horizontalLinear_eq, planarVelocity, hz, smul_zero,
      map_zero, zero_smul, add_zero]
  have hp := spatial_support q (subset_tsupport _ hV)
  have hz := closedCutoff_support (by norm_num : (-2 : ℝ) < -1)
    (by norm_num : (1 : ℝ) < 2) hχ
  have h₀ := hp (0 : Fin 2)
  have h₁ := hp (1 : Fin 2)
  norm_num [rectangleCollar, rectangle] at h₀ h₁
  constructor <;> intro j <;> fin_cases j
  · exact h₀.1
  · exact h₁.1
  · exact hz.1.le
  · exact h₀.2
  · exact h₁.2
  · exact hz.2.le

theorem velocity_support (q : Plane) (t : ℝ) :
    tsupport (fun x => velocity q (t, x)) ⊆ support := by
  change tsupport (BalancedStretch.push (fun x => raw q (t,x))) ⊆
    BalancedStretch.stretch '' rawSupport
  exact BalancedStretch.push_support (a := fun x => raw q (t,x)) (K := rawSupport)
    (isCompact_Icc : IsCompact rawSupport).isClosed (raw_support q t)

theorem planarVelocity_divergence (q : Plane) (t : ℝ) (x : Plane) :
    PlanarHamiltonian.divergence (planarVelocity q t) x = 0 := by
  have he : planarVelocity q t = field (fun y => pulse t * potential q y) := by
    funext y
    exact (field_const_mul ((rectangleCutoff_smooth rectangle 1).mul
      (translationPotential_smooth _)) _ _).symm
  rw [he]
  exact field_divergence (contDiff_const.mul
    ((rectangleCutoff_smooth rectangle 1).mul (translationPotential_smooth _))) x

theorem raw_divergence (q : Plane) (t : ℝ) (x : Space) :
    divergence (fun y => raw q (t, y)) x = 0 := by
  have hs : ContDiff ℝ ∞ (planarVelocity q t) :=
    (contDiff_const : ContDiff ℝ ∞ (fun _ : Plane => pulse t)).smul (spatial_smooth q)
  rw [show (fun y => raw q (t, y)) =
    CompactLift.spatial BalancedBody.verticalCutoff (planarVelocity q t) from rfl,
    CompactLift.spatial_divergence BalancedBody.verticalCutoff_smooth hs,
    planarVelocity_divergence, mul_zero]

theorem velocity_divergence (q : Plane) : Solenoidal (velocity q) :=
  BalancedStretch.velocity_divergence (raw_divergence q)

end ForcedComputation.BalancedLoader

end

end OAI
