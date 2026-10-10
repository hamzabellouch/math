import OAI.NumberTheory.CubicMoment.Estimates.StructuredMomentTwists
import OAI.NumberTheory.CubicMoment.Estimates.CommonFirstSmallSecondConductor

namespace OAI

/-! The literal structured character moment, with numerator v and
coprimality exclusion e, for fixed smooth coordinate weights. -/
noncomputable section
open Set Filter
open scoped ContDiff BigOperators
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem first_common_structured_exponents (hpub : PrimitiveResidueHeckeInput)
    (hperiod : CubicSupplementaryPeriodicity)
    {c : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hposV : tsupport V ⊆ Ioi 0)
    (hsmV : ContDiff ℝ ∞ V) (hVlo : ∀ x, x < 1 → V x = 0) (hVhi : ∀ x, 2 < x → V x = 0)
    (hVnorm : ∀ x, ‖V x‖ ≤ 1)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/10000 ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ (W : γ → ι → ℝ → ℂ), UniformLogWeights (fun z : γ × ι => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → ∃ Y₀ : ℝ,
      ∀ (r : γ) (Y N : ℝ) (X : ι → ℝ) (v e : Eisenstein) (u : ℝ) (P Q : Finset Eisenstein),
      Y₀ ≤ Y → 1 ≤ Real.log Y → Y^(1-δ) ≤ N → N ≤ Y^(1+δ) →
      (∀ i, (2*Y)^c < X i) → (∀ i, X i ≤ Y^2) → v ≠ 0 → e ≠ 0 →
      norm v ≤ Y^δ → norm e ≤ Y^δ → |u| ≤ Y^(721/2000:ℝ) →
      (∀ a ∈ P, gramDyad N a) → (∀ b ∈ Q, primary b ∧ norm b ≤ Y^δ) →
      (∑ b ∈ Q, ∑ a ∈ P, ‖structuredPrimeMoment a b v e u (W r) X V Y‖^2) ≤
        Y^(7/3-ε) := by
  obtain ⟨κ,hκ,hκhi,ε,hε,hfamily⟩ := first_common_small_second_exponents (γ := γ) (ι := ι)
    hpub hc hc₁ V hV hposV hsmV hVlo hVhi hVnorm hGI hGQ
  let δ := κ/3
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδκ : δ ≤ κ := by dsimp [δ]; linarith
  obtain ⟨T₁,hT₁⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop hδ).eventually_ge_atTop (81:ℝ))
  refine ⟨δ,hδ,hδκ.trans hκhi,ε,hε,?_⟩
  intro W hW hWlo
  obtain ⟨T₀,hraw⟩ := hfamily W hW hWlo
  refine ⟨max 1 (max T₀ T₁),?_⟩
  intro r Y N X v e u P Q hYT hlog hNlo hNhi hXlo hXhi hv he hvY heY hu hP hQ
  have hY1 : 1 ≤ Y := (le_max_left _ _).trans hYT
  have hYT₀ : T₀ ≤ Y := (le_max_left _ _).trans ((le_max_right _ _).trans hYT)
  have hYT₁ : T₁ ≤ Y := (le_max_right _ _).trans ((le_max_right _ _).trans hYT)
  have hq : ∀ _i : ι, structuredTwistModulus v e ≠ 0 :=
    fun _ => structuredTwistModulus_ne_zero hv he
  have hqY : ∀ _i : ι, norm (structuredTwistModulus v e) ≤ Y^κ := fun _ =>
    structuredTwistModulus_bound hY1 (by dsimp [δ]; linarith) (hT₁ Y hYT₁) hvY heY
  have hh := hraw r Y N X (fun _ => structuredTwistModulus v e)
    (fun _ => structuredTwistCharacter hperiod v e hv) (fun _ => u) P Q hYT₀ hlog
    ((Real.rpow_le_rpow_of_exponent_le hY1 (by linarith)).trans hNlo)
    (hNhi.trans (Real.rpow_le_rpow_of_exponent_le hY1 (by linarith))) hXlo hXhi hq
    (fun _ => structuredTwistCharacter_units hperiod v e hv) hqY (fun _ => hu) hP
    (fun b hb => ⟨(hQ b hb).1,(hQ b hb).2.trans
      (Real.rpow_le_rpow_of_exponent_le hY1 hδκ)⟩)
  convert hh using 1
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro a ha
  rw [structuredPrimeMoment_eq_tuple hperiod a b v e (hP a ha).1 (hQ b hb).1 hv u (W r) X V Y]
  rfl

end CubicFirstMoment

end

end OAI
