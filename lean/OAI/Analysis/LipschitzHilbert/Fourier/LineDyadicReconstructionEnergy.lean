import OAI.Analysis.LipschitzHilbert.Fourier.DyadicLineResolution
import OAI.Analysis.LipschitzHilbert.Fourier.LineAnnularSum
import OAI.Analysis.LipschitzHilbert.Fourier.LineDyadicSpectrum
import OAI.Analysis.LipschitzHilbert.Trees.DyadicLineGrid

namespace OAI

/-! Finite dyadic square bounds control the whole Schwartz function,
using the already proved strong binary resolution. -/
noncomputable section
open MeasureTheory Filter
open scoped FourierTransform BigOperators Topology
namespace LipschitzHilbert.PacketRepresentation
open DyadicLineGrid

theorem dyadicResolutionScale_eq_scale (N n : ℕ) :
    dyadicResolutionScale N n=scale ((n:ℤ)-(N:ℤ)) := by
  simp only [dyadicResolutionScale,scale,zpow_sub₀ (by norm_num : (2:ℝ)≠0),zpow_natCast]
  rw [one_div,inv_pow]
  ring

def dyadicResolutionWindow (N : ℕ) : Finset ℤ :=
  (Finset.range (2*N+1)).image (fun n : ℕ => (n:ℤ)-(N:ℤ))

theorem dyadicSchwartzSum_eq_window (N : ℕ) (f : SchwartzMap ℝ ℂ) :
    dyadicSchwartzSum N f=∑ k∈dyadicResolutionWindow N,
      lineSchwartzProjection dyadicDifference (scale k) (scale_pos k).ne' f := by
  classical
  unfold dyadicSchwartzSum dyadicResolutionWindow
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro n _
    simp only [dyadicResolutionScale_eq_scale]
  · intro i _ j _ hij
    change (i:ℤ)-(N:ℤ)=(j:ℤ)-(N:ℤ) at hij
    omega

theorem line_dyadic_reconstruction_energy (f : SchwartzMap ℝ ℂ) (C : ℝ)
    (hC : ∀ I : Finset ℤ, (∑ k∈I, ∫ x, ‖lineSchwartzProjection dyadicDifference
      (scale k) (scale_pos k).ne' f x‖^2)≤C) :
    (∫ x, ‖f x‖^2)≤3*C := by
  have hs (N : ℕ) : (∫ x, ‖dyadicSchwartzSum N f x‖^2)≤3*C := by
    rw [dyadicSchwartzSum_eq_window]
    have ho := line_annular_sum_energy (dyadicResolutionWindow N)
      (fun k => lineSchwartzProjection dyadicDifference (scale k) (scale_pos k).ne' f) (by
        intro k _ eta heta
        have hf := dyadicProjection_frequency (scale k) (scale_pos k) f eta heta
        have hlo := (div_le_iff₀ (scale_pos k)).mp hf.1
        have hhi := (le_div_iff₀ (scale_pos k)).mp hf.2
        constructor
        · change 1≤|eta| *scale k at hlo
          dsimp [scale] at hlo
          nlinarith only [hlo]
        · dsimp [scale] at hhi
          nlinarith only [hhi])
    exact ho.trans (mul_le_mul_of_nonneg_left (hC _) (by norm_num))
  have hn (g : SchwartzMap ℝ ℂ) : ‖g.toLp 2 volume‖^2=∫ x, ‖g x‖^2 :=
    memLp_toL2_norm_sq volume g (g.memLp 2 volume)
  have hl := (dyadicSchwartzSum_Lp_tendsto f).norm.pow 2
  have hb : ∀ᶠ N : ℕ in atTop, ‖(dyadicSchwartzSum N f).toLp 2 volume‖^2≤3*C :=
    Filter.Eventually.of_forall (fun N => by simpa only [hn] using hs N)
  simpa only [hn] using le_of_tendsto hl hb

end LipschitzHilbert.PacketRepresentation

end

end OAI
