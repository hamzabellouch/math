import OAI.NumberTheory.CubicMoment.Estimates.FullOrdinaryMoment
import OAI.NumberTheory.CubicMoment.Estimates.SmallConductorLogPowers

namespace OAI

/-! The part of the small-conductor range above a fixed logarithmic
power has arbitrary logarithmic saving, without any roughness or height
restriction. All coefficients remain the actual prime convolution. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem small_conductor_log_saving (hHuxley : HuxleyAdditiveLargeSieve)
    {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    {R : ℝ} (hR : 1 ≤ R) (hlo : ∀ r i x, x < 1 → W r i x = 0)
    (hhi : ∀ r i x, R < x → W r i x = 0) (k : ℕ) :
    ∃ (C : ℝ) (A : ℕ), 0 < C ∧ ∀ (r : γ) (X : ι → ℝ) (U V : ℝ)
      (v e : Eisenstein) (u : ℝ) (Ram S T J H : Finset Eisenstein),
      1 ≤ L r → (∀ i, 1 ≤ X i) → (∏ i, X i) = L r → 1 ≤ U → 1 ≤ V →
      (U*V)^2 ≤ L r → (1+Real.log (L r))^A ≤ U*V^2 →
      (∀ s ∈ S, primary s ∧ Squarefree s ∧ norm s ≤ U) →
      (∀ t ∈ T, primary t ∧ Squarefree t ∧ norm t ≤ V) →
      H ⊆ coprimeResidualSupport Ram J (coprimePairs S T) →
      (∑ h ∈ H, ‖fullStructuredPrimeSum R h 1 v e u (W r) X‖^2) ≤
        C*(Ram.card:ℝ)*J.card*(L r)^2*(U*V^2)^(1/3:ℝ)/(1+Real.log (L r))^k := by
  obtain ⟨C,a,hC,hbound⟩ := full_ordinary_moment hHuxley hW hR
    (by norm_num : (0:ℝ) < 1/12) hlo hhi
  refine ⟨2*C,4*(a+k),by positivity,?_⟩
  intro r X U V v e u Ram S T J H hL hX hprod hU hV hsize hlarge hS hT hH
  exact ordinary_log_tail_bound hC.le (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (zero_le_one.trans hL) hU hV (by linarith [Real.log_nonneg hL]) a k hsize hlarge
    (hbound r X U V v e u Ram S T J H hL hX hprod hU hV hS hT hH)

end CubicFirstMoment

end

end OAI
