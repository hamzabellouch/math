import OAI.NumberTheory.CubicMoment.Estimates.FullKummerLogSaving
import OAI.NumberTheory.CubicMoment.Estimates.PrimeConductorScale

namespace OAI

/-! The full nonprincipal rough-prime convolution at low height, with the
numerator measured at the actual full length, including its ramified and
unit factors. All prime and squarefree restrictions remain in the conclusion. -/
noncomputable section
open Filter
open scoped BigOperators
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem rough_kummer_low_height
    (hSW : KummerPrimeSiegelWalfisz) {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    (hlo : ∀ r i x, x < 1 → W r i x = 0)
    {c d R A : ℝ} (hc : 0 < c) (hd : 0 ≤ d) (hR : 1 ≤ R) (hA : 0 < A)
    (k U : ℕ) (hk : 0 < k) :
    ∃ K L₀ : ℝ, 0 < K ∧ ∀ (r : γ) (X : ι → ℝ), L₀ ≤ L r →
      (∏ i, X i) = L r → (∀ i, (L r)^c ≤ X i) →
      ∀ v : Eisenstein, v ≠ 0 → (¬∃ j : Eisenstein, j^3 = v) →
      norm v ≤ (Real.log (L r))^A →
      ∀ e : Eisenstein, e ≠ 0 → norm e ≤ (L r)^d → ∀ u : ℝ,
      |u| ≤ (1+Real.log (L r))^U →
      ‖fullStructuredPrimeSum R v 1 1 e u (W r) X‖ ≤
        K*L r/(1+Real.log (L r))^k := by
  obtain ⟨K,Y₀,L₁,hK,_,hbound⟩ := full_kummer_log_saving hSW hW hlo hc hd hR
    (show 0 < A+1 by linarith) k U hk
  have hevent : ∀ᶠ L : ℝ in atTop,
      L₁ ≤ L ∧ Y₀ ≤ L^c ∧ 1 ≤ Real.log L ∧
      ∀ Y : ℝ, L^c ≤ Y → (Real.log L)^A ≤ (Real.log Y)^(A+1) := by
    filter_upwards [eventually_ge_atTop L₁,
      (tendsto_rpow_atTop hc).eventually_ge_atTop Y₀,
      Real.tendsto_log_atTop.eventually_ge_atTop 1,
      rough_coordinate_conductor_scale hc hA.le] with L hL hY hlog hcon
    exact ⟨hL,hY,hlog,hcon⟩
  obtain ⟨L₀,hL₀⟩ := eventually_atTop.mp hevent
  refine ⟨K,L₀,hK,?_⟩
  intro r X hL hprod hrough v hv hn hcon e he heL u hu
  obtain ⟨hL₁,hY,hlog,hscale⟩ := hL₀ (L r) hL
  exact hbound r X (fun i => hY.trans (hrough i)) hL₁ hlog hprod hrough
    v hv hn (fun i => hcon.trans (hscale _ (hrough i)))
    e he heL u hu

end CubicFirstMoment

end

end OAI
