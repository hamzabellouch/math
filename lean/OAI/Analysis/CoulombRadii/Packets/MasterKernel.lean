import Mathlib
import OAI.Analysis.CoulombRadii.Packets.PacketWidthScalar
import OAI.Analysis.CoulombRadii.Packets.KernelCenterMass
import OAI.Analysis.CoulombRadii.FormDomain.WindowSquare

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology SchwartzMap
noncomputable section
namespace NeutralAtom

theorem master_kernel_estimates (g : 𝓢(Position,ℝ))
    (hg : ∀ x, 1 < ‖x‖ → g x=0) (hm : (∫ x, g x^2)=1) :
    ∃ C : ℝ, 0 < C ∧ ∀ {c r₀ s : ℝ}, 0 < c → 0 < r₀ → 0 < s →
    c*(1+packetExponent)*s^packetExponent ≤ 1/4 →
    ∀ y : Position,
      (∀ z, packetKernel g c r₀ s z y≠0 → ‖y-z‖ ≤ 2*packetWidth c r₀ s y) ∧
      (∀ z, |packetKernel g c r₀ s z y| ≤ C/(packetWidth c r₀ s y)^3) ∧
      (∀ z z', |packetKernel g c r₀ s z y-packetKernel g c r₀ s z' y| ≤
        (C/(packetWidth c r₀ s y)^4)*‖z-z'‖) ∧
      Integrable (fun z => packetKernel g c r₀ s z y) ∧
      |(∫ z, packetKernel g c r₀ s z y)-1| ≤
        C*(c*(1+packetExponent)*s^packetExponent) := by
  obtain ⟨B,L,hB,hL,hφ,hφL⟩ := schwartz_square_bounded_lipschitz g
  let A := 8*B
  let D := 64*B+80*L
  let M := (64*Real.pi/3)*(48*B+64*L)
  let C := 1+A+D+M
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hAC : A ≤ C := by dsimp [C]; linarith
  have hDC : D ≤ C := by dsimp [C]; linarith
  have hMC : M ≤ C := by dsimp [C]; linarith
  refine ⟨C,by dsimp [C]; linarith,?_⟩
  intro c r₀ s hc hr hs hsmall y
  let t := packetWidth c r₀ s
  let q := c*(1+packetExponent)*s^packetExponent
  have ht : ∀ z, 0 < t z := packetWidth_pos hc hr hs
  have hq : 0 ≤ q := by
    dsimp [q]
    exact mul_nonneg (mul_nonneg hc.le (by norm_num [packetExponent]))
      (Real.rpow_nonneg hs.le _)
  have hlip : ∀ z z', |t z-t z'| ≤ q*‖z-z'‖ := packetWidth_lipschitz hc.le hr hs
  have hlip' : ∀ z z', |t z-t z'| ≤ ‖z-z'‖/4 := by
    intro z z'
    calc
      _ ≤ q*‖z-z'‖ := hlip z z'
      _ ≤ (1/4)*‖z-z'‖ := mul_le_mul_of_nonneg_right hsmall (norm_nonneg _)
      _ = _ := by ring
  have hφs : ∀ x, 1 < ‖x‖ → (fun z => g z^2) x=0 := by
    intro x hx; simp only [hg x hx,zero_pow (by decide : (2:ℕ)≠0)]
  have he (z : Position) : packetKernel g c r₀ s z y=scaledCenterKernel (fun z => g z^2) t z y := rfl
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro z hK
    rw [he] at hK
    have hh := (scaledCenterKernel_support_width _ t hφs ht hlip' z y hK).2
    linarith [ht y]
  · intro z
    rw [he]
    exact (scaledCenterKernel_uniform_bound _ t hB hφs hφ ht hlip' z y).trans
      (div_le_div_of_nonneg_right hAC (pow_nonneg (ht y).le _))
  · intro z z'
    rw [he,he]
    exact (scaledCenterKernel_center_lipschitz _ t hB hL hφs hφ hφL ht hlip' z z' y).trans
      (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hDC (pow_nonneg (ht y).le _)) (norm_nonneg _))
  · exact integrable_scaledCenterKernel (g.continuous.pow 2) (continuous_packetWidth c r₀ s) ht hφs hlip' y
  · have hh := center_kernel_mass_defect hB hL hq hsmall (g.continuous.pow 2)
      (continuous_packetWidth c r₀ s) ht hφs hφ hφL hlip y
    change |(∫ z, packetKernel g c r₀ s z y)-(∫ z, g z^2)| ≤ M*q at hh
    rw [hm] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hMC hq)

end NeutralAtom
end

end
end

end OAI
