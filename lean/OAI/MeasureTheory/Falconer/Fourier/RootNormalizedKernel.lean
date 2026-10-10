import OAI.MeasureTheory.Falconer.Fourier.RootKernelTerms
import OAI.MeasureTheory.Falconer.Shells.HighShellNormalization

namespace OAI

namespace PlanarFalconer
open MeasureTheory

noncomputable def rootAbsorbedCoefficient (d e : RootEndpointData) (N : ℕ) (sig : ℝ) (j : ℕ) (b : ℂ × (RootMaskIndex → ℕ)) : ℂ :=
  b.1 * ((2:ℝ)^(-(j:ℝ)*((N:ℝ)-0))*rootAssignmentScale d e N sig b.2 : ℝ)

noncomputable def rootNormalizedKernel (d e : RootEndpointData) (N : ℕ) (sig : ℝ) (n : ℕ)
    (r : ℝ) (ψ : UnitCircle → ℂ) (z : Plane × Plane) : ℂ :=
  (((r*(2:ℝ)^(-(0:ℝ)))^(1/2:ℝ):ℝ):ℂ) * ∑ j ∈ Finset.range (n+1),
    ((((r/(2:ℝ)^(N:ℝ))⁻¹)^j:ℝ):ℂ) *
      ((inverseLeibnizTerms j (rootMaskIndices d e)).map (fun b =>
        rootAbsorbedCoefficient d e N sig j b *
          (((((dist z.1 z.2/(2:ℝ)^(-(0:ℝ)))⁻¹)^j:ℝ):ℂ) *
            sourceDistanceKernel ψ (rootLeftSymbol d N sig b.2)
              (rootRightSymbol e N sig b.2) r z.1 z.2))).sum

 theorem root_weightedInverseCircle_normalized (d e : RootEndpointData)
    (hd : 0 < d.Q.side) (he : 0 < e.Q.side) (N : ℕ) (sig : ℝ) (n : ℕ) {r : ℝ} (hr : 0 < r) {z : Plane × Plane} (hz : 0 < dist z.1 z.2)
    (ψ : UnitCircle → ℂ) (hψ : Measurable ψ) {P : ℝ} (hP : 0 ≤ P)
    (hp : ∀ dir, ‖ψ dir‖ ≤ P) :
    (((dist z.1 z.2/(2:ℝ)^(-(0:ℝ)))^(-(1/2:ℝ)):ℝ):ℂ) *
      sourceInverseCircleIntegral n r (z.1-z.2) ψ (rootPairSymbol d e N sig z) =
      rootNormalizedKernel d e N sig n r ψ z := by
  rw [root_inverseCircleIntegral_kernel_terms d e hd he N sig n ψ hψ hP hp r z,
    ← mul_assoc, ← Complex.ofReal_mul,
    high_shell_weight_cancellation hr hz (by positivity)]
  unfold rootNormalizedKernel
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Complex.ofReal_pow, high_shell_inverse_power_split]
  simp only [Complex.ofReal_mul, ← List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro b hb
  simp only [rootAbsorbedCoefficient, Complex.ofReal_mul]
  ring

end PlanarFalconer

end OAI
