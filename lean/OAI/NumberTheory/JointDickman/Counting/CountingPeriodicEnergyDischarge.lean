import OAI.NumberTheory.JointDickman.Counting.CountingPeriodicEnergy
import OAI.NumberTheory.JointDickman.Counting.CountingForwardEnergyDischarge

namespace OAI

/-! # Application consequences of the proved short-average estimates -/
namespace JointDickman
open Finset Filter MeasureTheory Classical PublishedInputs
open scoped Topology

theorem counting_periodic_energy_proved
    (hKMT : CharacterDistanceDivergence) (hM : PrimeReciprocalMertensInput)
    (hSD : SquarefreeSelbergDelangeInput) (hSW : SquarefreeCharacterEstimateInput)
    (hMP : PrimeProductMertensInput)
    {J : ℕ} (hJ : 0 < J) (ζ : Fin (J-1) → ℂ) (hζ : ∀ i, ‖ζ i‖ = 1)
    (μ : ℂ) (hμ : ‖μ‖ ≤ 1)
    (hmean : ∀ D : ℝ, 0 < D → Tendsto (centeredBinPrefix J ζ μ D) atTop (𝓝 0))
    (P : MvPolynomial (Fin 4) ℝ) (m : (Fin 4 →₀ ℕ) → ℕ) (hm : ∀ d, 0 < m d)
    (c : (Fin 4 →₀ ℕ) → ℕ → ℝ)
    (hc : ∀ d, c d 0 = squarefreeLeadingConstant (1/2)) (D : (Fin 4 →₀ ℕ) → ℕ)
    {η : ℝ} (hη : 0 < η) {q : ℕ} [NeZero q]
    (F : ZMod q → ℝ) (W : ℝ) (hF : ∀ r, |F r| ≤ W)
    (A scale : ℕ → ℝ) (T H R M : ℕ → ℕ) (L : ℕ) (τ C : ℝ)
    (hA : ∀ B, 0 < A B) (hscale : Tendsto scale atTop atTop)
    (hR : Tendsto R atTop atTop)
    (hRT : Tendsto (fun B => (R B : ℝ)/(T B : ℝ)) atTop (𝓝 0))
    (hvalid : ∀ᶠ B in atTop, 0 < T B ∧ Real.log (T B) ≤ (B : ℝ)/10 ∧ η*T B ≤ H B)
    (hMpos : ∀ᶠ B in atTop, 0 < M B)
    {V : ℝ} (hV : 0 ≤ V) (hroot : ∀ᶠ B in atTop, independentRootMean B L τ C ≤ V) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ B in atTop, ∀ᶠ n in atTop,
      ∀ (σ : ℕ → ℝ), (∀ u, |σ u| ≤ 3) →
      let z := fun k => binLabel (fun j : Fin (J-1) => primeBin (scale n) J (j.val+1)) ζ k-μ
      (1/(A B*scale n))*(∑ u ∈ Ico ⌈A B*scale n⌉₊ ⌊2*(A B*scale n)⌋₊,
        (‖complexEnergy (countingArithmeticKernel (fun j => F (j : ZMod q)) P m B L
          (T B) (H B) (M B) u τ C c D (σ u))
          (fun i => z (u+(i.val+1)))‖/(M B : ℝ))^2) < ε := by
  intro ε hε
  have hrows := counting_forward_row_energy_proved hKMT hM hSD hSW hMP hJ ζ hζ μ hμ
    hmean P m hm c hc D hη F W hF A scale T H R M L τ C hA hscale hR hRT hvalid hV hroot
    (ε/8) (by positivity)
  filter_upwards [hrows,hMpos] with B hB hMB
  filter_upwards [hB,(hscale.const_mul_atTop (hA B)).eventually_gt_atTop 0] with n hn hX
  intro σ hσ z
  let S := Ico ⌈A B*scale n⌉₊ ⌊2*(A B*scale n)⌋₊
  apply (symmetric_energy_square_mean hMB S
    (fun u => countingArithmeticKernel (fun j => F (j : ZMod q)) P m B L
      (T B) (H B) (M B) u τ C c D (σ u))
    (fun u i => z (u+(i.val+1)))
    (fun u i k => countingArithmeticKernel_symm ..)
    (fun u i => countingArithmeticKernel_diag ..) hX
    (fun i => (hn σ hσ i).le)).trans_lt
  linarith

end JointDickman

end OAI
