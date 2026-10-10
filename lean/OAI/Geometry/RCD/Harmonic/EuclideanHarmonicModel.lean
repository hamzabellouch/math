import OAI.Geometry.RCD.Harmonic.LocalAffineMoments
import OAI.Geometry.RCD.Coordinates.EuclideanAffineTaylor
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic

namespace OAI

/-! # The Euclidean harmonic model in the affine-improvement limit

The model retains its actual function, local L² representatives, and
normalization. No affine approximation property is included in its data.
-/

open Set Metric MeasureTheory
open scoped InnerProductSpace ENNReal

noncomputable section
namespace RegularPointCoordinates

/-- Each standard coordinate belongs to L² on a finite Euclidean ball. -/
theorem euclideanCoordinate_memLp (n : ℕ) (r : ℝ) (i : Fin n) :
    MemLp (fun z : Euclidean n => z i) 2 (volume.restrict (ball 0 r)) := by
  let : IsFiniteMeasure (volume.restrict (ball (0 : Euclidean n) r)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      (measure_ball_lt_top (μ := (volume : Measure (Euclidean n))) (x := 0) (r := r))⟩
  apply MemLp.of_bound (EuclideanSpace.proj i).continuous.aestronglyMeasurable |r|
  filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
  have hz' : ‖z‖ < r := by simpa only [mem_ball, dist_zero_right] using hz
  exact (PiLp.norm_apply_le z i).trans (hz'.le.trans (le_abs_self r))

def euclideanCoordinateLp (n : ℕ) (r : ℝ) (i : Fin n) :
    Lp ℝ 2 (volume.restrict (ball (0 : Euclidean n) r)) :=
  (euclideanCoordinate_memLp n r i).toLp (fun z => z i)

theorem euclideanCoordinateLp_coe (n : ℕ) (r : ℝ) (i : Fin n) :
    euclideanCoordinateLp n r i =ᵐ[volume.restrict (ball 0 r)] fun z => z i :=
  MemLp.coeFn_toLp _

/-- An L²-normalized harmonic function on the limiting Euclidean ball. -/
structure EuclideanHarmonicModel (n : ℕ) (S : ℝ) where
  value : Euclidean n → ℝ
  harmonic : InnerProductSpace.HarmonicOnNhd value (ball 0 S)
  memLp : MemLp value 2 (volume.restrict (ball 0 S))
  normalized : ‖normalizeLocalL2 volume (ball 0 S) measure_ball_ne_top
    (memLp.toLp value)‖ ≤ 1

def EuclideanHarmonicModel.localLp {n : ℕ} {S : ℝ}
    (w : EuclideanHarmonicModel n S) {r : ℝ} (hr : r ≤ S) :
    Lp ℝ 2 (volume.restrict (ball (0 : Euclidean n) r)) :=
  (w.memLp.mono_measure (Measure.restrict_mono_set volume (ball_subset_ball hr))).toLp w.value

theorem EuclideanHarmonicModel.localLp_coe {n : ℕ} {S r : ℝ}
    (w : EuclideanHarmonicModel n S) (hr : r ≤ S) :
    w.localLp hr =ᵐ[volume.restrict (ball 0 r)] w.value := MemLp.coeFn_toLp _

/-- Target, constant and identity coordinates, all in the normalized
local L² space. Their finite moments are the compactness output needed. -/
def EuclideanHarmonicModel.moments {n : ℕ} {S r : ℝ}
    (w : EuclideanHarmonicModel n S) (hr : r ≤ S) :
    Option (Option (Fin n)) → Lp ℝ 2 (volume.restrict (ball (0 : Euclidean n) r)) :=
  affineMomentFamily n
    (normalizeLocalL2 volume (ball 0 r) measure_ball_ne_top (w.localLp hr))
    (normalizeLocalL2 volume (ball 0 r) measure_ball_ne_top
      (restrictedOne volume (ball 0 r) measure_ball_ne_top))
    (fun i => normalizeLocalL2 volume (ball 0 r) measure_ball_ne_top
      (euclideanCoordinateLp n r i))

/-- Evans, PDE (second edition), §2.2.3(c), Theorem 7, degree two,
combined with Cauchy--Schwarz on the outer ball. The input only bounds the
second derivative of a normalized Euclidean harmonic function. -/
def EuclideanHarmonicHessianInput (n : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ S : ℝ, 0 < S → ∀ w : EuclideanHarmonicModel n S,
    ∀ z ∈ ball (0 : Euclidean n) (S / 2),
      ‖fderiv ℝ (fderiv ℝ w.value) z‖ ≤ C / S ^ 2

end RegularPointCoordinates

end

end OAI
