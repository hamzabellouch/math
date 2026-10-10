import OAI.NumberTheory.CubicMoment.Decomposition.StoppedReflectedMellin
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedSignedMellin

namespace OAI

/-! The actual stopped coefficients satisfy the full two-sign coprimality
Mellin bound. Its normalization is the exact Jacobian 1/(4π). -/
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stopped_norm_mellin_integral
    (hpnt : PrimaryPrimePNT) (hSW : KummerPrimeSiegelWalfisz)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    {ξ κ E F J : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hκ : 0 < κ)
    (hF : 0 ≤ F) (hJ : 0 ≤ J)
    (m : ℝ) (hm : 0 < m) (Φ : ℝ → ℂ) (hΦ : HasCompactSupport Φ)
    (hΦ' : ContDiff ℝ ∞ Φ) (k q H : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (δ l b u V B : ℝ), 0 < δ → δ ≤ 1 → (Real.log X)^(-J) ≤ δ →
      1 ≤ l → X^κ ≤ b → b ≤ X →
      0 ≤ V → |u| ≤ (Real.log X)^H → 1+V ≤ (Real.log X)^F →
      1 ≤ B → B ≤ b^(3/5:ℝ) →
      ∀ W : ι → ℝ → ℂ, (∀ i x, ‖W i x‖ ≤ 1) → (∀ i, ContDiff ℝ ∞ (W i)) →
      (∀ i x, 0 < x → ‖deriv (W i) x‖*x ≤ V) →
      ∀ (S U : Finset Eisenstein),
      (∀ v ∈ S, v ≠ 0 ∧ norm v ≤ B ∧ ¬∃ n : Eisenstein, n^3 = v) →
      (∀ p ∈ U, primaryPrime p) →
      ∀ e : Eisenstein, e ≠ 0 → norm e ≤ X^E →
      ∀ (j₀ k₀ h : ℕ) (Z Q : ℝ) (early : Bool), j₀ ≤ h →
      2 < min (X^ξ) (geometricBinLower (1+δ) X h) →
      2*(Real.log X)^(2*(4*(k+2)+k)) ≤
        min (X^ξ) (geometricBinLower (1+δ) X h) →
      ∀ {N : ℝ}, 0 < N → ∀ ρ : ℝ, 0 ≤ ρ →
      (1+ρ)^q*(∫ t : ℝ, ‖normDenominatorMellinCoefficient m hm Φ hΦ hΦ' ρ t‖*
        coprimeMellinMass (stoppedIntervalSupport ι X l b e) S U
          (fun n => star (stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) u W
            (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
              j₀ k₀ h Z Q early) n))
          (fun n => star (stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) u W
            (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
              j₀ k₀ h Z Q early) n))
          (fun n => norm n/N) t) ≤ K*b^2*B^(1/3:ℝ)/(Real.log X)^k := by
  obtain ⟨Kp,hKp,hplus⟩ := stopped_arithmetic_mellin_integral (ι := ι) (E := E)
    hpnt hSW hMV hC hHuxley hξ hξz hκ hF hJ m hm Φ hΦ hΦ' k q H
  obtain ⟨Kn,hKn,hminus⟩ := stopped_reflected_arithmetic_mellin_integral (ι := ι) (E := E)
    hpnt hSW hMV hC hHuxley hξ hξz hκ hF hJ m hm Φ hΦ hΦ' k q H
  refine ⟨(Kp+Kn)/(4*Real.pi),by positivity,?_⟩
  filter_upwards [hplus,hminus] with X hplus hminus
  intro δ l b u V B hδ hδone hwidth hl hb hbX hV hu hVF hB hBb W hW hWi hWd
    S U hS hU e he hNe j₀ k₀ h Z Q early hj hR hRL N hN ρ hρ
  have hp := hplus δ l b u V B hδ hδone hwidth hl hb hbX hV hu hVF hB hBb
    W hW hWi hWd S U hS hU e he hNe j₀ k₀ h Z Q early hj hR hRL ρ hρ
  have hn := hminus δ l b u V B hδ hδone hwidth hl hb hbX hV hu hVF hB hBb
    W hW hWi hWd S U hS hU e he hNe j₀ k₀ h Z Q early hj hR hRL ρ hρ
  let selected := stoppedSideTest (geometricPrimeBin (1+δ) X)
    (geometricBinLower (1+δ) X) j₀ k₀ h Z Q early
  have hid := divisor_normMellin_signed_integral m hm Φ hΦ hΦ'
    (stoppedIntervalSupport ι X l b e) S U
    (stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) 0 W selected)
    (fun n hn => (stoppedIntervalSupport_spec X l b e hn).1) u ρ hN
  simp only [twistedCoprimeMellinMass,←stoppedRowCoefficient_phase,
    ←stoppedDivisorMass_eq] at hid
  change (1+ρ)^q*(∫ t : ℝ, ‖normDenominatorMellinCoefficient m hm Φ hΦ hΦ' ρ t‖*
    coprimeMellinMass (stoppedIntervalSupport ι X l b e) S U
      (fun n => star (stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) u W selected n))
      (fun n => star (stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) u W selected n))
      (fun n => norm n/N) t) ≤ _
  rw [hid]
  calc
    _ = ((1+ρ)^q*(∫ t : ℝ, ‖arithmeticMellinCoefficient m hm Φ hΦ hΦ' ρ t‖*
          stoppedDivisorMass X (X^ξ) (X^(2/5:ℝ)) l b (t+u) W selected e S U)+
        (1+ρ)^q*(∫ t : ℝ, ‖arithmeticMellinCoefficient m hm Φ hΦ hΦ' ρ (-t)‖*
          stoppedDivisorMass X (X^ξ) (X^(2/5:ℝ)) l b (t+u) W selected e S U))/(4*Real.pi) := by ring
    _ ≤ (Kp*b^2*B^(1/3:ℝ)/(Real.log X)^k+
          Kn*b^2*B^(1/3:ℝ)/(Real.log X)^k)/(4*Real.pi) :=
      div_le_div_of_nonneg_right (add_le_add hp hn) (by positivity)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
