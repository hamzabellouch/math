import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.ScalarBounds
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.VelocityDetectorScales

namespace OAI

/-! The prescribed rational burst duration makes the scalar diffusion error
strictly smaller than the detector's fixed observation gap. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set

theorem scalar_burst_error (C L n : ℕ)
    {a : ℝ → Plane → Plane} {h w v : ℝ → Plane → ℝ}
    (hw : TorusScalarSolution (2 * (duration C L n : ℝ)) 1 a h w (fun _ => 0))
    (hv : TorusScalarSolution (2 * (duration C L n : ℝ)) 1 a
      (fun t x => h t x - scalarLaplacian (v t) x) v (fun _ => 0))
    (hlap : ∀ t ∈ Icc 0 (2 * (duration C L n : ℝ)), ∀ x,
      |scalarLaplacian (v t) x| ≤ (laplacianBound C L n : ℝ)) :
    ∀ t ∈ Icc 0 (2 * (duration C L n : ℝ)), ∀ x, |w t x - v t x| < 1 / 16 := by
  have hd : (0 : ℝ) < duration C L n := by exact_mod_cast duration_pos C L n
  have hD : (0 : ℝ) ≤ laplacianBound C L n := by
    exact_mod_cast laplacianBound_nonneg C L n
  have hs : (2 : ℝ) * (duration C L n : ℝ) * (laplacianBound C L n : ℝ) < 1 / 16 := by
    have hh := (Rat.cast_lt (K := ℝ)).mpr (diffusion_loss_small C L n)
    norm_num only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] at hh
    exact hh
  have he := hw.stability hv (by positivity) (by norm_num)
    (E := 0) (D := (laplacianBound C L n : ℝ))
    (fun t ht x => by simpa only [sub_sub_cancel] using hlap t ht x)
    (fun _ => by simp)
  intro t ht x
  calc
    _ ≤ (laplacianBound C L n : ℝ) * t := by simpa only [zero_add] using he t ht x
    _ ≤ (laplacianBound C L n : ℝ) * (2 * (duration C L n : ℝ)) :=
      mul_le_mul_of_nonneg_left ht.2 hD
    _ < 1 / 16 := by nlinarith

/-- The same comparison includes all older injections through their small
value at the start of this burst; no decomposition of the scalar is needed. -/
theorem scalar_burst_error_initial (C L n : ℕ)
    {a : ℝ → Plane → Plane} {h w v : ℝ → Plane → ℝ} {w₀ v₀ : Plane → ℝ}
    (hw : TorusScalarSolution (2 * (duration C L n : ℝ)) 1 a h w w₀)
    (hv : TorusScalarSolution (2 * (duration C L n : ℝ)) 1 a
      (fun t x => h t x - scalarLaplacian (v t) x) v v₀)
    (hlap : ∀ t ∈ Icc 0 (2 * (duration C L n : ℝ)), ∀ x,
      |scalarLaplacian (v t) x| ≤ (laplacianBound C L n : ℝ))
    {E : ℝ} (hinit : ∀ x, |w₀ x - v₀ x| ≤ E) :
    ∀ t ∈ Icc 0 (2 * (duration C L n : ℝ)), ∀ x,
      |w t x - v t x| < E + 1 / 16 := by
  have hd : (0 : ℝ) < duration C L n := by exact_mod_cast duration_pos C L n
  have hD : (0 : ℝ) ≤ laplacianBound C L n := by
    exact_mod_cast laplacianBound_nonneg C L n
  have hs : (2 : ℝ) * (duration C L n : ℝ) * (laplacianBound C L n : ℝ) < 1 / 16 := by
    have hh := (Rat.cast_lt (K := ℝ)).mpr (diffusion_loss_small C L n)
    norm_num only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] at hh
    exact hh
  have he := hw.stability hv (by positivity) (by norm_num)
    (E := E) (D := (laplacianBound C L n : ℝ))
    (fun t ht x => by simpa only [sub_sub_cancel] using hlap t ht x) hinit
  intro t ht x
  calc
    _ ≤ E + (laplacianBound C L n : ℝ) * t := he t ht x
    _ ≤ E + (laplacianBound C L n : ℝ) * (2 * (duration C L n : ℝ)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left ht.2 hD)
    _ < E + 1 / 16 := by nlinarith

end ForcedComputation.VelocityDetector

end

end OAI
