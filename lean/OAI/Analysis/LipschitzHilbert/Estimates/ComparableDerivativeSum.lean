import OAI.Analysis.LipschitzHilbert.Estimates.ComparableDerivativeSupport
import OAI.Analysis.LipschitzHilbert.Fourier.LineDyadicReconstructionEnergy

namespace OAI

/-! The derivative part of the comparable-frequency commutator sums
uniformly, including arbitrarily low output frequencies. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation
open DyadicLineGrid

def comparableDerivativePiece (m b : SchwartzMap ℝ ℂ)
    (H : ℤ → SchwartzMap ℝ ℂ) (k : ℤ) : SchwartzMap ℝ ℂ :=
  schwartzDerivative 1 (lineSchwartzCommutator m
    (lineSchwartzProjection dyadicDifference (scale k) (scale_pos k).ne' b) (H k))

theorem comparableDerivativeSum_energy (I : Finset ℤ) (m b : SchwartzMap ℝ ℂ)
    (H : ℤ → SchwartzMap ℝ ℂ) (A L : ℝ)
    (hm : ∀ eta, ‖m eta‖≤A) (hLip : ∀ x y, ‖b x-b y‖≤L*|x-y|)
    (hH : ∀ k∈I, ∀ eta, (𝓕 (H k) : SchwartzMap ℝ ℂ) eta≠0 → |eta|≤64/scale k) :
    (∫ x, ‖(∑ k∈I, comparableDerivativePiece m b H k) x‖^2)≤
      48*(16384*(A*L*(∫ t, |t| *‖(𝓕⁻ dyadicDifference : SchwartzMap ℝ ℂ) t‖)*
        (52*Real.pi/3)))^2*(∑ k∈I, ∫ x, ‖H k x‖^2) := by
  let C₀ := A*L*(∫ t, |t| *‖(𝓕⁻ dyadicDifference : SchwartzMap ℝ ℂ) t‖)*(52*Real.pi/3)
  let C := 16384*C₀
  let F := ∑ k∈I, comparableDerivativePiece m b H k
  let P := fun i k => lineSchwartzProjection dyadicDifference (scale i) (scale_pos i).ne'
    (comparableDerivativePiece m b H k)
  have hpiece (i k : ℤ) (hk : k∈I) : (∫ x, ‖P i k x‖^2)≤
      (lineScaleWeight i k)^2*(C^2*(∫ x, ‖H k x‖^2)) := by
    by_cases hr : scale k/scale i≤128
    · have hc := projectedCommutator_derivative_energy m b (H k) (scale k) (scale i) A L
        (scale_pos k) (scale_pos i) hm hLip
      have hratio := bounded_scaleRatio_le_weight i k hr
      calc
        _ ≤ (C₀*(scale k/scale i))^2*(∫ x, ‖H k x‖^2) := hc
        _ = C₀^2*(scale k/scale i)^2*(∫ x, ‖H k x‖^2) := by ring
        _ ≤ C₀^2*(16384*lineScaleWeight i k)^2*(∫ x, ‖H k x‖^2) := by
          gcongr
          exact div_nonneg (scale_pos k).le (scale_pos i).le
        _ = _ := by dsimp [C]; ring
    · have hlarge : 128*scale i≤scale k :=
        (le_div_iff₀ (scale_pos i)).mp (lt_of_not_ge hr).le
      have hz := comparableDerivative_projection_zero m b (H k) (scale k) (scale i)
        (scale_pos k) (scale_pos i) hlarge (hH k hk)
      change (∫ x, ‖lineSchwartzProjection dyadicDifference (scale i) (scale_pos i).ne'
        (comparableDerivativePiece m b H k) x‖^2)≤_
      simp only [comparableDerivativePiece,hz,zero_apply,norm_zero,zero_pow (by decide : 2≠0),integral_zero]
      positivity
  have hproj (J : Finset ℤ) : (∑ i∈J, ∫ x, ‖lineSchwartzProjection dyadicDifference
      (scale i) (scale_pos i).ne' F x‖^2)≤16*C^2*(∑ k∈I, ∫ x, ‖H k x‖^2) := by
    have hs := line_geometric_energy_schur J I (fun i k x => P i k x)
      (fun i _ k _ => (P i k).memLp 2 volume)
      (fun k => C^2*(∫ x, ‖H k x‖^2)) (fun k _ => by positivity)
      (fun i _ k hk => hpiece i k hk)
    have he (i : ℤ) : lineSchwartzProjection dyadicDifference (scale i) (scale_pos i).ne' F=
        ∑ k∈I, P i k := map_sum (lineSchwartzProjectionLM dyadicDifference (scale i) (scale_pos i).ne') _ I
    simp_rw [he,sum_apply]
    simpa only [←Finset.mul_sum,mul_assoc] using hs
  have hh := line_dyadic_reconstruction_energy F (16*C^2*(∑ k∈I, ∫ x, ‖H k x‖^2)) hproj
  apply hh.trans_eq
  dsimp [C,C₀]
  ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
