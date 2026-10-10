import OAI.NumberTheory.CubicMoment.Decomposition.StoppedBoundedDivisor
import OAI.NumberTheory.CubicMoment.Estimates.NormCoprimeWindow

namespace OAI

/-! The complete Mellin line for bounded squarefree coefficients.  All
coprimality rows are retained, and the coefficient bound is uniform in
both signs and every translated height. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ContDiff FourierTransform SchwartzMap
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem bounded_divisor_character_mass (hpnt : PrimaryPrimePNT)
    (hHuxley : HuxleyAdditiveLargeSieve) :
    ∃ (K : ℝ) (d : ℕ), 0 < K ∧ ∀ (S H U : Finset Eisenstein)
      (β : Eisenstein → ℂ) (N M B u : ℝ), 65536 ≤ N → 0 ≤ M → 1 ≤ B →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ norm a ≤ N) →
      (∀ a ∈ S, ‖β a‖ ≤ M) → (∀ p ∈ U, primaryPrime p) →
      8*B ≤ N^(3/4:ℝ) → (∀ v ∈ H, v ≠ 0 ∧ norm v ≤ B) →
      divisorCharacterMass S H U β u ≤ K*M^2*N^2*B^(1/3:ℝ)*(1+Real.log N)^d := by
  obtain ⟨K,d,hK,hbound⟩ := bounded_divisor_all_frequency_mass hpnt hHuxley
  refine ⟨K,d,hK,?_⟩
  intro S H U β N M B u hN hM hB hS hβ hU hsize hH
  let γ := fun a : Eisenstein => β a*mellinPhase u (norm a)
  have hγ : ∀ a ∈ S, ‖γ a‖ ≤ M := by
    intro a ha
    simpa only [γ,norm_mul,mellinPhase_norm,mul_one] using hβ a ha
  have hm := hbound S H U γ N M B hN hM hB hS hγ hU hsize hH
  have he : divisorCharacterMass S H U β u =
      ∑ s ∈ U.powerset, ∑ v ∈ H,
        ‖∑ a ∈ S.filter (fun a => (∏ p ∈ s,p) ∣ a), γ a*cubicSymbol a v‖^2 := by
    unfold divisorCharacterMass finiteCharacterMass
    apply Finset.sum_congr rfl
    intro s hs
    apply Finset.sum_congr rfl
    intro v hv
    congr 2
    apply Finset.sum_congr rfl
    intro a ha
    dsimp [γ]
    ring
  rw [he]
  exact hm

theorem bounded_coprime_mellin_integral (hpnt : PrimaryPrimePNT)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (m : ℝ) (hm : 0 < m) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) (q : ℕ) :
    ∃ (K : ℝ) (d : ℕ), 0 < K ∧ ∀ (S H U : Finset Eisenstein)
      (β : Eisenstein → ℂ) (N M B u ρ L : ℝ),
      65536 ≤ N → 0 ≤ M → 1 ≤ B → 0 ≤ ρ → 0 < L →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ norm a ≤ N) →
      (∀ a ∈ S, ‖β a‖ ≤ M) → (∀ p ∈ U, primaryPrime p) →
      8*B ≤ N^(3/4:ℝ) → (∀ v ∈ H, v ≠ 0 ∧ norm v ≤ B) →
      (1+ρ)^q*(∫ t : ℝ, ‖normDenominatorMellinCoefficient m hm W hW hW' ρ t‖*
        twistedCoprimeMellinMass S H U β (fun a => norm a/L) u t) ≤
      K*M^2*N^2*B^(1/3:ℝ)*(1+Real.log N)^d := by
  obtain ⟨K,d,hK,hbound⟩ := bounded_divisor_character_mass hpnt hHuxley
  obtain ⟨D,hD,hdecay⟩ := normDenominatorMellinCoefficient_moment_decay m hm W hW hW' q 0
  refine ⟨D*K,d,mul_pos hD hK,?_⟩
  intro S H U β N M B u ρ L hN hM hB hρ hL hS hβ hU hsize hH
  have hlog : 0 ≤ 1+Real.log N := by
    have hN1 : 1 ≤ N := by linarith
    linarith [Real.log_nonneg hN1]
  let A := K*M^2*N^2*B^(1/3:ℝ)*(1+Real.log N)^d
  let g := twistedCoprimeMellinMass S H U β (fun a => norm a/L) u
  have hg : Continuous g :=
    coprimeMellinMass_continuous S H U
      (fun a => star (β a*mellinPhase u (norm a)))
      (fun a => star (β a*mellinPhase u (norm a))) (fun a => norm a/L)
  have hg0 : ∀ t, 0 ≤ g t :=
    coprimeMellinMass_nonneg S H U _ _ _
  have hgA (t : ℝ) : g t ≤ A := by
    dsimp only [g]
    rw [twistedCoprimeMellinMass_eq_divisor_mass S H U β (fun a ha => (hS a ha).1) u t hL]
    have h₁ := hbound S H U β N M B (u+2*Real.pi*t) hN hM hB hS hβ hU hsize hH
    have h₂ := hbound S H U β N M B (u-2*Real.pi*t) hN hM hB hS hβ hU hsize hH
    dsimp only [A]
    linarith
  have hi := (normDenominatorMellinCoefficient_integrable m hm W hW hW' ρ).norm
  have hig : Integrable (fun t : ℝ =>
      ‖normDenominatorMellinCoefficient m hm W hW hW' ρ t‖*g t) :=
    hi.mul_bdd hg.aestronglyMeasurable (Eventually.of_forall (fun t => by
      rw [Real.norm_eq_abs,abs_of_nonneg (hg0 t)]
      exact hgA t))
  have hh : (∫ t : ℝ, ‖normDenominatorMellinCoefficient m hm W hW hW' ρ t‖*g t) ≤
      (∫ t : ℝ, ‖normDenominatorMellinCoefficient m hm W hW hW' ρ t‖)*A := by
    rw [←integral_mul_const]
    exact integral_mono hig (hi.mul_const A) (fun t =>
      mul_le_mul_of_nonneg_left (hgA t) (_root_.norm_nonneg _))
  have hd : (1+ρ)^q*(∫ t : ℝ, ‖normDenominatorMellinCoefficient m hm W hW hW' ρ t‖) ≤ D := by
    simpa only [pow_zero,one_mul] using hdecay ρ hρ
  calc
    _ ≤ (1+ρ)^q*((∫ t : ℝ, ‖normDenominatorMellinCoefficient m hm W hW hW' ρ t‖)*A) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ = ((1+ρ)^q*(∫ t : ℝ, ‖normDenominatorMellinCoefficient m hm W hW hW' ρ t‖))*A := by ring
    _ ≤ D*A := mul_le_mul_of_nonneg_right hd (by dsimp [A]; positivity)
    _ = _ := by dsimp [A]; ring

end CubicFirstMoment

end

end OAI
