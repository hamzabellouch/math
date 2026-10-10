import OAI.Probability.FreeIsing.Energy.ArtanhResponseCoefficients
import OAI.Probability.FreeIsing.Ising.CanonicalPosteriorStops
import OAI.Probability.FreeIsing.Ising.ContinuousRootResponse

namespace OAI

noncomputable section
open MeasureTheory
open scoped NNReal

namespace Problem367.IsingObservationFactor
open IsingObservationInnovation IsingCopyEnergy ArtanhMartingaleFormula

variable {d : ℕ} {beta : ℝ}

theorem continuousPosterior_variance_pos (v : TreeVertex d)
    (t : ℝ≥0) (x : Paths d) :
    0 < 1 - continuousPosterior beta v t x ^ 2 :=
  sub_pos.mpr (Real.tanh_sq_lt_one _)

theorem firstWeight_mul_continuousRootCovariance
    (hb : 0 ≤ beta) (v : TreeVertex d) (t : ℝ≥0) (x : Paths d) :
    firstWeight (continuousPosterior beta (ConnectedHull.root d) t x) *
      continuousRootCovariance hb v t x = continuousRootResponse hb v t x := by
  change (1 / (1 - continuousPosterior beta (ConnectedHull.root d) t x ^ 2)) *
    ((1 - continuousPosterior beta (ConnectedHull.root d) t x ^ 2) *
      continuousRootResponse hb v t x) = _
  rw [one_div, ← mul_assoc,
    inv_mul_cancel₀ (continuousPosterior_variance_pos (ConnectedHull.root d) t x).ne', one_mul]

theorem continuousRootCovariance_div_variance
    (hb : 0 ≤ beta) (v : TreeVertex d) (t : ℝ≥0) (x : Paths d) :
    continuousRootCovariance hb v t x /
      (1 - continuousPosterior beta (ConnectedHull.root d) t x ^ 2) =
        continuousRootResponse hb v t x := by
  rw [← ArtanhResponseCoefficients.firstWeight_mul]
  exact firstWeight_mul_continuousRootCovariance hb v t x

theorem continuousRootCovariance_square_tsum
    (hb : 0 ≤ beta) (t : ℝ≥0) (x : Paths d) :
    (∑' v, continuousRootCovariance hb v t x ^ 2) =
      (1 - continuousPosterior beta (ConnectedHull.root d) t x ^ 2) ^ 2 *
        (∑' v, continuousRootResponse hb v t x ^ 2) := by
  simp only [continuousRootCovariance, continuousPosterior, mul_pow, tsum_mul_left]

theorem secondWeight_mul_continuousRootCovariance_square_tsum
    (hb : 0 ≤ beta) (t : ℝ≥0) (x : Paths d) :
    secondWeight (continuousPosterior beta (ConnectedHull.root d) t x) *
      (∑' v, continuousRootCovariance hb v t x ^ 2) =
        continuousPosterior beta (ConnectedHull.root d) t x *
          (∑' v, continuousRootResponse hb v t x ^ 2) := by
  rw [ArtanhResponseCoefficients.secondWeight_mul_tsum_sq]
  simp_rw [continuousRootCovariance_div_variance]

theorem continuousRootCovariance_square_tsum_le_response
    (hb : 0 ≤ beta) (t : ℝ≥0) (x : Paths d) :
    (∑' v, continuousRootCovariance hb v t x ^ 2) ≤
      ∑' v, continuousRootResponse hb v t x ^ 2 := by
  rw [continuousRootCovariance_square_tsum]
  have h0 := (continuousPosterior_variance_pos (beta := beta) (ConnectedHull.root d) t x).le
  have h1 : 1 - continuousPosterior beta (ConnectedHull.root d) t x ^ 2 ≤ 1 :=
    sub_le_self _ (sq_nonneg _)
  exact mul_le_of_le_one_left (tsum_nonneg (fun _ => sq_nonneg _))
    (pow_le_one₀ h0 h1)

theorem abs_continuousPosterior_mul_response_square_tsum_le
    (hb : 0 ≤ beta) (t : ℝ≥0) (x : Paths d) :
    |continuousPosterior beta (ConnectedHull.root d) t x *
      (∑' v, continuousRootResponse hb v t x ^ 2)| ≤
        ∑' v, continuousRootResponse hb v t x ^ 2 := by
  rw [abs_mul, abs_of_nonneg (show 0 ≤ ∑' v, continuousRootResponse hb v t x ^ 2
    from tsum_nonneg (fun _ => sq_nonneg _))]
  exact mul_le_of_le_one_left (tsum_nonneg (fun _ => sq_nonneg _))
    (abs_lt.mpr (continuousPosterior_interior beta (ConnectedHull.root d) t x)).le

theorem firstWeight_mul_stopped_continuousRootCovariance
    (hb : 0 ≤ beta) (v : TreeVertex d) (τ : Paths d → WithTop ℝ≥0)
    (t : ℝ≥0) (x : Paths d) :
    firstWeight (stoppedProcess (continuousPosterior beta (ConnectedHull.root d)) τ t x) *
      stoppedProcess (continuousRootCovariance hb v) τ t x =
        stoppedProcess (continuousRootResponse hb v) τ t x :=
  firstWeight_mul_continuousRootCovariance hb v _ x

theorem firstWeight_stopped_mul_continuousRootCovariance_of_le
    (hb : 0 ≤ beta) (v : TreeVertex d) (τ : Paths d → WithTop ℝ≥0)
    (t : ℝ≥0) (x : Paths d) (ht : (t : WithTop ℝ≥0) ≤ τ x) :
    firstWeight (stoppedProcess (continuousPosterior beta (ConnectedHull.root d)) τ t x) *
      continuousRootCovariance hb v t x = continuousRootResponse hb v t x := by
  rw [stoppedProcess_eq_of_le ht]
  exact firstWeight_mul_continuousRootCovariance hb v t x

theorem firstWeight_stopped_pullback_mul_continuousRootCovariance_of_le
    {Ω : Type*} (hb : 0 ≤ beta) (v : TreeVertex d) (φ : Ω → Paths d)
    (τ : Ω → WithTop ℝ≥0) (t : ℝ≥0) (ω : Ω)
    (ht : (t : WithTop ℝ≥0) ≤ τ ω) :
    firstWeight (stoppedProcess
      (fun s ω => continuousPosterior beta (ConnectedHull.root d) s (φ ω)) τ t ω) *
      continuousRootCovariance hb v t (φ ω) = continuousRootResponse hb v t (φ ω) := by
  rw [stoppedProcess_eq_of_le ht]
  exact firstWeight_mul_continuousRootCovariance hb v t (φ ω)

theorem firstWeight_stopped_copy_mul_continuousRootCovariance_of_le
    (hb : 0 ≤ beta) (v : TreeVertex d) (j : Bool)
    (τ : Joint d → WithTop ℝ≥0) (t : ℝ≥0) (q : Joint d)
    (ht : (t : WithTop ℝ≥0) ≤ τ q) :
    firstWeight (stoppedProcess
      (copyContinuousPosterior beta (ConnectedHull.root d) j) τ t q) *
      continuousRootCovariance hb v t (projection j q) =
        continuousRootResponse hb v t (projection j q) :=
  firstWeight_stopped_pullback_mul_continuousRootCovariance_of_le hb v
    (projection j) τ t q ht

end Problem367.IsingObservationFactor

end

end OAI
