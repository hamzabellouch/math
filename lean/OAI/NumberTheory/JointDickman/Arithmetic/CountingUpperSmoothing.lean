import OAI.NumberTheory.JointDickman.Counting.CountingUpperVariation
import OAI.NumberTheory.JointDickman.Arithmetic.ResidueSmoothingIdentity

namespace OAI

/-! # Short progression smoothing of the actual counting coefficient -/
namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem counting_lag_upper_smoothing
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (P : MvPolynomial (Fin 4) ℝ) (d : Fin 4 →₀ ℕ)
    {m : ℕ} (hm : 0 < m) (c : ℕ → ℝ) (hc : c 0 = squarefreeLeadingConstant (1/2))
    (D : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ B : ℕ in atTop, ∀ (T H U : ℕ) (σ : ℝ),
      0 < T → 0 < U → U ≤ T → Real.log T ≤ (B : ℝ)/10 → η*T ≤ H → |σ| ≤ 3 →
      ∀ (a b : Fin m) (q R v : ℕ) (F : ZMod q → ℝ) (g : ℕ → ℂ) (G W : ℝ),
        0 < R → (∀ n, ‖g n‖ ≤ G) → (∀ r, |F r| ≤ W) →
      let K := cutLagWeight H U (fun j => countingTermCoefficient P d m B j c D T σ a b/(j : ℝ))
      ‖(∑ j ∈ range (T+1), (K j : ℂ)*(F (j : ZMod q) : ℂ)*g (v+j))-
        ∑ j ∈ range (T+1), (K j : ℂ)*(F (j : ZMod q) : ℂ)*residueSmoothed g q R (v+j)‖ ≤
          (W*G*C)*(q*R : ℕ)/T := by
  obtain ⟨C,hC,hvar⟩ := counting_lag_upper_variation hM hMP P d hm c hc D hη
  refine ⟨C,hC,?_⟩
  filter_upwards [hvar] with B hB
  intro T H U σ hT hU hUT hlog hH hσ a b q R v F g G W hR hG hF K
  have hG0 : 0 ≤ G := (norm_nonneg (g 0)).trans (hG 0)
  have hW0 : 0 ≤ W := (abs_nonneg (F 0)).trans (hF 0)
  apply (periodicConvolution_smoothing K g F hR T v hG hF).trans
  have hv := hB T H U σ hT hU hUT hlog hH hσ a b
  calc
    _ ≤ W*G*(C/(T : ℝ))*(q*R : ℕ) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hv (mul_nonneg hW0 hG0)) (Nat.cast_nonneg _)
    _ = _ := by ring

end JointDickman

end OAI
