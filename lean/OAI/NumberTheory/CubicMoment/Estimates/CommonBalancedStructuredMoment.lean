import OAI.NumberTheory.CubicMoment.Estimates.StructuredMomentTwists
import OAI.NumberTheory.CubicMoment.Estimates.CommonSquarefreePrimeExponents

namespace OAI

/-! The literal structured character moment, with numerator v and
coprimality exclusion e, for fixed smooth coordinate weights. -/
noncomputable section
open Set Filter
open scoped ContDiff BigOperators
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem balanced_common_structured_exponents (hpub : PrimitiveResidueHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve)
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
      ∀ (r : γ) (Y : ℝ) (X : ι → ℝ) (v e : Eisenstein) (u : ℝ)
        (P : Finset (Eisenstein × Eisenstein)),
      Y₀ ≤ Y → 1 ≤ Real.log Y →
      (∀ i, (2*Y)^c < X i) → (∀ i, X i ≤ Y^2) → v ≠ 0 → e ≠ 0 →
      norm v ≤ Y^δ → norm e ≤ Y^δ → |u| ≤ Y^(721/2000:ℝ) →
      (∀ a ∈ P, PrimarySquarefreePair a ∧ norm a.1 ≤ Y^(1/3+δ) ∧
        norm a.2 ≤ Y^(1/3+δ) ∧ Y^(1/3-δ) ≤ norm a.1) →
      (∑ a ∈ P, ‖structuredPrimeMoment a.1 a.2 v e u (W r) X V Y‖^2) ≤ Y^(7/3-ε) := by
  obtain ⟨κ,hκ,hκhi,ε,hε,hfamily⟩ := balanced_common_squarefree_exponents (γ := γ) (ι := ι)
    hpub hHuxley hc hc₁ V hV hposV hsmV hVlo hVhi hVnorm hGI hGQ
  let δ := min κ (1/100000)/3
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδκ : δ ≤ κ := by dsimp [δ]; linarith [min_le_left κ (1/100000)]
  obtain ⟨T₁,hT₁⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop hδ).eventually_ge_atTop (81:ℝ))
  refine ⟨δ,hδ,hδκ.trans hκhi,ε,hε,?_⟩
  intro W hW hWlo
  obtain ⟨T₀,hraw⟩ := hfamily W hW hWlo
  refine ⟨max 1 (max T₀ T₁),?_⟩
  intro r Y X v e u P hYT hlog hXlo hXhi hv he hvY heY hu hP
  have hY1 : 1 ≤ Y := (le_max_left _ _).trans hYT
  have hYT₀ : T₀ ≤ Y := (le_max_left _ _).trans ((le_max_right _ _).trans hYT)
  have hYT₁ : T₁ ≤ Y := (le_max_right _ _).trans ((le_max_right _ _).trans hYT)
  have hq : ∀ _i : ι, structuredTwistModulus v e ≠ 0 :=
    fun _ => structuredTwistModulus_ne_zero hv he
  have hqY : ∀ _i : ι, norm (structuredTwistModulus v e) ≤ Y^(1/100000:ℝ) := fun _ =>
    structuredTwistModulus_bound hY1 (by dsimp [δ]; linarith [min_le_right κ (1/100000)]) (hT₁ Y hYT₁) hvY heY
  have hPκ : ∀ a ∈ P, PrimarySquarefreePair a ∧ norm a.1 ≤ Y^(1/3+κ) ∧
      norm a.2 ≤ Y^(1/3+κ) ∧ Y^(1/1000:ℝ) ≤ norm a.1 := by
    intro a ha
    have hupp : Y^(1/3+δ) ≤ Y^(1/3+κ) :=
      Real.rpow_le_rpow_of_exponent_le hY1 (by linarith)
    have hlo : Y^(1/1000:ℝ) ≤ Y^(1/3-δ) :=
      Real.rpow_le_rpow_of_exponent_le hY1 (by linarith)
    exact ⟨(hP a ha).1,(hP a ha).2.1.trans hupp,(hP a ha).2.2.1.trans hupp,
      hlo.trans (hP a ha).2.2.2⟩
  have hh := hraw r Y X (fun _ => structuredTwistModulus v e)
    (fun _ => structuredTwistCharacter hperiod v e hv) (fun _ => u) P hYT₀ hlog hXlo hXhi hq
    (fun _ => structuredTwistCharacter_units hperiod v e hv) hqY (fun _ => hu) hPκ
  convert hh using 1
  apply Finset.sum_congr rfl
  intro a ha
  rw [structuredPrimeMoment_eq_tuple hperiod a.1 a.2 v e (hP a ha).1.1 (hP a ha).1.2.1 hv u (W r) X V Y]
  rfl

end CubicFirstMoment

end

end OAI
