import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

namespace OAI

/-!
# Collision model for periodic hard spheres

The normal parametrization and absolute angular kernel here are exactly those of
Sections 1–2 of the paper.
-/

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace BoltzmannNonuniqueness

abbrev Velocity := EuclideanSpace ℝ (Fin 3)
abbrev Position := Fin 3 → AddCircle (1 : ℝ)
abbrev Phase := Position × Velocity
abbrev Density := Phase → ℝ
abbrev Sphere := Metric.sphere (0 : Velocity) 1

/-- Ordinary surface area, rather than normalized probability on the sphere. -/
def sphereArea : Measure Sphere := (volume : Measure Velocity).toSphere

def normalComponent (v w ω : Velocity) : ℝ := inner ℝ (v - w) ω

def scatterLeft (v w ω : Velocity) : Velocity := v - normalComponent v w ω • ω

def scatterRight (v w ω : Velocity) : Velocity := w + normalComponent v w ω • ω

def collisionKernel (v w ω : Velocity) : ℝ := |normalComponent v w ω|

def gain (f : Density) (x : Position) (v : Velocity) : ℝ :=
  ∫ p : Velocity × Sphere,
    collisionKernel v p.1 p.2 * f (x, scatterLeft v p.1 p.2) *
      f (x, scatterRight v p.1 p.2)
    ∂((volume : Measure Velocity).prod sphereArea)

def loss (f : Density) (x : Position) (v : Velocity) : ℝ :=
  ∫ p : Velocity × Sphere,
    collisionKernel v p.1 p.2 * f (x, v) * f (x, p.1)
    ∂((volume : Measure Velocity).prod sphereArea)

def collision (f : Density) (x : Position) (v : Velocity) : ℝ :=
  gain f x v - loss f x v

theorem collisionKernel_nonneg (v w ω : Velocity) : 0 ≤ collisionKernel v w ω :=
  abs_nonneg _

theorem scatter_momentum (v w ω : Velocity) :
    scatterLeft v w ω + scatterRight v w ω = v + w := by
  unfold scatterLeft scatterRight
  abel

theorem scatter_energy (v w ω : Velocity) (hω : ‖ω‖ = 1) :
    ‖scatterLeft v w ω‖ ^ 2 + ‖scatterRight v w ω‖ ^ 2 = ‖v‖ ^ 2 + ‖w‖ ^ 2 := by
  unfold scatterLeft scatterRight normalComponent
  rw [norm_sub_sq_real, norm_add_sq_real]
  simp only [inner_smul_right, norm_smul, Real.norm_eq_abs, hω, mul_one, sq_abs,
    inner_sub_left]
  ring

theorem normalComponent_scatter (v w ω : Velocity) (hω : ‖ω‖ = 1) :
    normalComponent (scatterLeft v w ω) (scatterRight v w ω) ω =
      -normalComponent v w ω := by
  simp only [normalComponent, scatterLeft, scatterRight, inner_sub_left, inner_add_left,
    real_inner_smul_left, real_inner_self_eq_norm_sq, hω]
  ring

theorem scatterLeft_involutive (v w ω : Velocity) (hω : ‖ω‖ = 1) :
    scatterLeft (scatterLeft v w ω) (scatterRight v w ω) ω = v := by
  change scatterLeft v w ω -
    normalComponent (scatterLeft v w ω) (scatterRight v w ω) ω • ω = v
  rw [normalComponent_scatter v w ω hω]
  simp [scatterLeft, neg_smul]

theorem scatterRight_involutive (v w ω : Velocity) (hω : ‖ω‖ = 1) :
    scatterRight (scatterLeft v w ω) (scatterRight v w ω) ω = w := by
  change scatterRight v w ω +
    normalComponent (scatterLeft v w ω) (scatterRight v w ω) ω • ω = w
  rw [normalComponent_scatter v w ω hω]
  simp [scatterRight, neg_smul]

theorem collisionKernel_scatter (v w ω : Velocity) (hω : ‖ω‖ = 1) :
    collisionKernel (scatterLeft v w ω) (scatterRight v w ω) ω =
      collisionKernel v w ω := by
  simp only [collisionKernel, normalComponent_scatter v w ω hω, abs_neg]

theorem scatterLeft_translate (v w u ω : Velocity) :
    scatterLeft (v - u) (w - u) ω = scatterLeft v w ω - u := by
  have h : v - u - (w - u) = v - w := by abel
  simp only [scatterLeft, normalComponent, h]
  abel

theorem scatterRight_translate (v w u ω : Velocity) :
    scatterRight (v - u) (w - u) ω = scatterRight v w ω - u := by
  have h : v - u - (w - u) = v - w := by abel
  simp only [scatterRight, normalComponent, h]
  abel

/-- The center may vary with space and time: this identity is pointwise in the center. -/
theorem scatter_centered_energy (v w u ω : Velocity) (hω : ‖ω‖ = 1) :
    ‖scatterLeft v w ω - u‖ ^ 2 + ‖scatterRight v w ω - u‖ ^ 2 =
      ‖v - u‖ ^ 2 + ‖w - u‖ ^ 2 := by
  simpa only [scatterLeft_translate, scatterRight_translate] using
    scatter_energy (v - u) (w - u) ω hω

/-- A Gaussian with arbitrary amplitude, exponent, and center. -/
def gaussian (A β : ℝ) (u v : Velocity) : ℝ := A * Real.exp (-β * ‖v - u‖ ^ 2)

/-- Detailed balance, used for the transported Maxwellian barrier in Section 4. -/
theorem gaussian_detailed_balance (A β : ℝ) (u v w ω : Velocity) (hω : ‖ω‖ = 1) :
    gaussian A β u (scatterLeft v w ω) * gaussian A β u (scatterRight v w ω) =
      gaussian A β u v * gaussian A β u w := by
  have h := scatter_centered_energy v w u ω hω
  unfold gaussian
  calc
    A * Real.exp (-β * ‖scatterLeft v w ω - u‖ ^ 2) *
        (A * Real.exp (-β * ‖scatterRight v w ω - u‖ ^ 2)) =
        A ^ 2 * Real.exp (-β * (‖scatterLeft v w ω - u‖ ^ 2 +
          ‖scatterRight v w ω - u‖ ^ 2)) := by rw [mul_add, Real.exp_add]; ring
    _ = A ^ 2 * Real.exp (-β * (‖v - u‖ ^ 2 + ‖w - u‖ ^ 2)) := by rw [h]
    _ = A * Real.exp (-β * ‖v - u‖ ^ 2) * (A * Real.exp (-β * ‖w - u‖ ^ 2)) := by
      rw [mul_add, Real.exp_add]
      ring

/-- Pointwise detailed balance proves equality of the gain and loss integrands. -/
theorem gaussian_gain_eq_loss (A β : ℝ) (u : Velocity) (x : Position) (v : Velocity) :
    gain (fun z => gaussian A β u z.2) x v =
      loss (fun z => gaussian A β u z.2) x v := by
  apply integral_congr_ae
  filter_upwards [] with p
  have hω : ‖(p.2 : Velocity)‖ = 1 := mem_sphere_zero_iff_norm.mp p.2.property
  rw [mul_assoc, gaussian_detailed_balance A β u v p.1 p.2 hω, ← mul_assoc]

/-- This algebraic identity alone does not assert collision integrability for arbitrary `β`.
The admissibility interface separately requires genuine finite collision integrals. -/
theorem gaussian_collision_eq_zero (A β : ℝ) (u : Velocity) (x : Position)
    (v : Velocity) : collision (fun z => gaussian A β u z.2) x v = 0 := by
  exact sub_eq_zero.mpr (gaussian_gain_eq_loss A β u x v)

end BoltzmannNonuniqueness

end

end OAI
