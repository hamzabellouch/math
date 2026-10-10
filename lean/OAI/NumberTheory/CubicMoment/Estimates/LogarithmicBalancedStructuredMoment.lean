import OAI.NumberTheory.CubicMoment.Estimates.StructuredWeightScaling
import OAI.NumberTheory.CubicMoment.Estimates.CommonBalancedStructuredMoment

namespace OAI

/-! The literal structured character moment, with numerator v and
coprimality exclusion e, for fixed smooth coordinate weights. -/
noncomputable section
open Set Filter
open scoped ContDiff BigOperators
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem balanced_logarithmic_structured_moment (hpub : PrimitiveResidueHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {c : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hposV : tsupport V ⊆ Ioi 0)
    (hsmV : ContDiff ℝ ∞ V) (hVlo : ∀ x, x < 1 → V x = 0) (hVhi : ∀ x, 2 < x → V x = 0)
    (hVnorm : ∀ x, ‖V x‖ ≤ 1)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/10000 ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
      LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → ∃ Y₀ : ℝ,
      ∀ (r : γ) (X : ι → ℝ) (v e : Eisenstein) (u : ℝ)
        (P : Finset (Eisenstein × Eisenstein)),
      Y₀ ≤ (L r) → 1 ≤ Real.log (L r) →
      (∀ i, (2*(L r))^c < X i) → (∀ i, X i ≤ (L r)^2) → v ≠ 0 → e ≠ 0 →
      norm v ≤ (L r)^δ → norm e ≤ (L r)^δ → |u| ≤ (L r)^(721/2000:ℝ) →
      (∀ a ∈ P, PrimarySquarefreePair a ∧ norm a.1 ≤ (L r)^(1/3+δ) ∧
        norm a.2 ≤ (L r)^(1/3+δ) ∧ (L r)^(1/3-δ) ≤ norm a.1) →
      (∑ a ∈ P, ‖structuredPrimeMoment a.1 a.2 v e u (W r) X V (L r)‖^2) ≤ (L r)^(7/3-ε) := by
  obtain ⟨δ,hδ,hδhi,ε,hε,hraw⟩ := balanced_common_structured_exponents
    (γ := γ) (ι := ι) hpub hHuxley hperiod hc hc₁ V hV hposV hsmV hVlo hVhi hVnorm hGI hGQ
  refine ⟨δ,hδ,hδhi,ε/2,by positivity,?_⟩
  intro L W hL hW hWlo
  let s := ε/(4*((Fintype.card ι:ℝ)+1))
  have hs : 0 < s := by dsimp [s]; positivity
  let U : γ → ι → ℝ → ℂ := fun r i x => ((L r^(-s):ℝ):ℂ)*W r i x
  have hU : UniformLogWeights (fun z : γ × ι => U z.1 z.2) := by
    have heq : (fun z : γ × ι => U z.1 z.2) =
        normalizedLogWeight (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) s := by
      funext z x
      simp only [U,normalizedLogWeight,Complex.real_smul]
    rw [heq]
    exact hW.normalize hs
  have hUlo : ∀ r i x, x < 1 → U r i x = 0 := by
    intro r i x hx
    simp only [U,hWlo r i x hx,mul_zero]
  obtain ⟨T,hbound⟩ := hraw U hU hUlo
  have hsd : 2*(s*(Fintype.card ι:ℝ)) ≤ ε/2 := by
    have heq : s*(4*((Fintype.card ι:ℝ)+1)) = ε := by
      dsimp [s]
      field_simp
    nlinarith
  refine ⟨T,?_⟩
  intro r X v e u P hT hlog hXlo hXhi hv he hvY heY hu hP
  have hb := hbound r (L r) X v e u P hT hlog hXlo hXhi hv he hvY heY hu hP
  exact normalized_energy_transfer P
    (fun z => structuredPrimeMoment z.1 z.2 v e u (W r) X V (L r))
    (fun z => structuredPrimeMoment z.1 z.2 v e u (U r) X V (L r)) (hL r)
    (fun z _ => structuredPrimeMoment_log_scaling z.1 z.2 v e u (W r) X V
      (zero_lt_one.trans_le (hL r)) s) hb hsd

end CubicFirstMoment

end

end OAI
