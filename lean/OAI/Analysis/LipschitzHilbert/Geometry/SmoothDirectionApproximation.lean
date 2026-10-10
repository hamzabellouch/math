import OAI.Analysis.LipschitzHilbert.Fourier.LineMollification

namespace OAI

/-! Actual compact smooth approximants of a bounded Lipschitz direction. -/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff Topology
namespace LipschitzHilbert.PacketRepresentation

def lineDirectionMollifier (n : ℕ) : ContDiffBump (0 : ℝ) where
  rIn := (1/((n:ℝ)+1))/2
  rOut := 1/((n:ℝ)+1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have h : 0<1/((n:ℝ)+1) := by positivity
    linarith

theorem lineDirectionMollifier_radius_tendsto :
    Tendsto (fun n => (lineDirectionMollifier n).rOut) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

variable (u : ℝ → ℝ) (hu : LipschitzWith 1 u) (hb : ∀ x, |u x|≤1)

def smoothDirectionApprox (n : ℕ) : SchwartzMap ℝ ℝ :=
  lineMollification (lineDirectionMollifier n) (compactDirectionCutoff u ((n:ℝ)+1))
    ((compactDirectionCutoff_lipschitz u hu hb ((n:ℝ)+1) (by positivity)).continuous.integrable_of_hasCompactSupport
      (compactDirectionCutoff_compact u ((n:ℝ)+1) (by positivity)))
    (compactDirectionCutoff_compact u ((n:ℝ)+1) (by positivity))

theorem smoothDirectionApprox_lipschitz (n : ℕ) :
    LipschitzWith 1 (smoothDirectionApprox u hu hb n : ℝ → ℝ) :=
  lineMollification_lipschitz _ _ _ _ (compactDirectionCutoff_lipschitz u hu hb _ (by positivity))

theorem smoothDirectionApprox_bound (n : ℕ) (x : ℝ) :
    |smoothDirectionApprox u hu hb n x|≤1 :=
  lineMollification_bound _ _ _ _ (compactDirectionCutoff_bound u hb _ (by positivity)) x

theorem smoothDirectionApprox_compact (n : ℕ) :
    HasCompactSupport (smoothDirectionApprox u hu hb n : ℝ → ℝ) :=
  lineMollification_compact _ _ _ _

theorem smoothDirectionApprox_tendsto (x : ℝ) :
    Tendsto (fun n => smoothDirectionApprox u hu hb n x) atTop (𝓝 (u x)) := by
  have hnorm : Tendsto (fun n => |smoothDirectionApprox u hu hb n x-
      compactDirectionCutoff u ((n:ℝ)+1) x|) atTop (𝓝 0) :=
    squeeze_zero (fun _ => abs_nonneg _)
      (fun n => lineMollification_approximation _ _ _ _
        (compactDirectionCutoff_lipschitz u hu hb _ (by positivity)) x)
      lineDirectionMollifier_radius_tendsto
  have hdiff : Tendsto (fun n => smoothDirectionApprox u hu hb n x-
      compactDirectionCutoff u ((n:ℝ)+1) x) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using hnorm)
  simpa only [sub_add_cancel,zero_add] using hdiff.add (compactDirectionCutoff_tendsto u x)

end LipschitzHilbert.PacketRepresentation

end

end OAI
