import OAI.Geometry.RCD.Sobolev.EuclideanWeakHarmonicSmoothing
import Mathlib.Analysis.Calculus.BumpFunction.Convolution

namespace OAI

/-! # Compact smooth mollifiers with an explicit shrinking radius -/

open Set Metric Filter MeasureTheory
open scoped ContDiff Convolution Topology
noncomputable section
namespace RegularPointCoordinates

def euclideanMollifierRadius (k : ℕ) : ℝ := 1/((k:ℝ)+1)

theorem euclideanMollifierRadius_pos (k : ℕ) : 0<euclideanMollifierRadius k := by
  unfold euclideanMollifierRadius
  positivity

theorem euclideanMollifierRadius_tendsto :
    Tendsto euclideanMollifierRadius atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

def euclideanMollifierBump (n k : ℕ) : ContDiffBump (0 : Euclidean n) :=
  ⟨euclideanMollifierRadius k/2,euclideanMollifierRadius k,
    half_pos (euclideanMollifierRadius_pos k),half_lt_self (euclideanMollifierRadius_pos k)⟩

def euclideanMollifier (n k : ℕ) : Euclidean n → ℝ :=
  (euclideanMollifierBump n k).normed volume

theorem euclideanMollifier_smooth (n k : ℕ) : ContDiff ℝ ∞ (euclideanMollifier n k) :=
  (euclideanMollifierBump n k).contDiff_normed

theorem euclideanMollifier_compact (n k : ℕ) : HasCompactSupport (euclideanMollifier n k) :=
  (euclideanMollifierBump n k).hasCompactSupport_normed

theorem euclideanMollifier_support (n k : ℕ) :
    tsupport (euclideanMollifier n k) ⊆ closedBall 0 (euclideanMollifierRadius k) := by
  rw [euclideanMollifier,(euclideanMollifierBump n k).tsupport_normed_eq]
  exact Subset.rfl

theorem euclideanMollifier_convolution_tendsto {n : ℕ} {f : Euclidean n → ℝ}
    (hf : Continuous f) (x : Euclidean n) :
    Tendsto (fun k => (euclideanMollifier n k ⋆[ContinuousLinearMap.mul ℝ ℝ,volume] f) x)
      atTop (𝓝 (f x)) := by
  have hL : ContinuousLinearMap.lsmul ℝ ℝ = ContinuousLinearMap.mul ℝ ℝ := by
    ext; rfl
  simpa only [euclideanMollifier,hL] using
    (ContDiffBump.convolution_tendsto_right_of_continuous
      (φ := euclideanMollifierBump n) (μ := volume) euclideanMollifierRadius_tendsto hf x)

theorem weak_harmonic_mollification {n : ℕ} {f : Euclidean n → ℝ} {S : ℝ}
    (hf : LocallyIntegrable f volume) (hw : EuclideanWeakHarmonicOn f S) (k : ℕ) :
    InnerProductSpace.HarmonicOnNhd
      (f ⋆[ContinuousLinearMap.mul ℝ ℝ,volume] euclideanMollifier n k)
      (ball 0 (S-euclideanMollifierRadius k)) :=
  weak_harmonic_convolution hf (euclideanMollifier_smooth n k)
    (euclideanMollifier_compact n k) (euclideanMollifier_support n k) hw

end RegularPointCoordinates

end

end OAI
