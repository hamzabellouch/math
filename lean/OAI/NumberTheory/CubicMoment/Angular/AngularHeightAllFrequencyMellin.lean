import OAI.NumberTheory.CubicMoment.Angular.AngularHeightAllFrequencyMass
import OAI.NumberTheory.CubicMoment.Estimates.HeightMellinWindow
import OAI.NumberTheory.CubicMoment.Estimates.FullStructuredHeightEnvelope
import OAI.NumberTheory.CubicMoment.Estimates.MellinWindowIntegral

namespace OAI

/-! Full-line Mellin transfer of every nonzero height-averaged frequency.
The arithmetic height interval and the Mellin variable are independent. -/
noncomputable section
open scoped BigOperators ContDiff
open Filter MeasureTheory
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_height_all_frequency_mellin_saving
    (hpub : PrimitiveAngularHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C c R : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hc : 0 < c) (hc₁ : c ≤ 1) (hR : 1 ≤ R)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
    (M : ℝ) (hM : 0 < M) (V : ℝ → ℂ) (hV : HasCompactSupport V)
    (hV' : ContDiff ℝ ∞ V) (k q : ℕ) :
    ∃ η σ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < σ ∧
    ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
      LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → (∀ r i x, R < x → W r i x = 0) →
    ∃ (K L₀ : ℝ) (m : ℕ), 0 < K ∧
      ∀ (r : γ) (X : ι → ℝ) (B : ℝ) (H : Finset Eisenstein)
        (e : Eisenstein) (u T ρ ε : ℝ), L₀ ≤ L r →
      (∏ i, X i) = L r → (∀ i, (2*L r)^c < X i) →
      1 ≤ B → B ≤ (L r)^(1+η) →
      (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B) →
      e ≠ 0 → norm e ≤ (L r)^σ → (1+Real.log (L r))^m ≤ T →
      T ≤ (L r)^(7/20:ℝ) → |u| ≤ (L r)^(7/20:ℝ) → 0 ≤ ρ → (ε = 1 ∨ ε = -1) →
      (1+ρ)^q*dyadicHeightMean (fun t => ∫ s : ℝ,
        ‖arithmeticMellinCoefficient M hM V hV hV' ρ (ε*s)‖*
          fullStructuredHeightMass R H 1 e ℓ 0 (W r) X (t+u+s)) T ≤
        K*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^k := by
  obtain ⟨η,σ,hη,hη₁,hσ,hmass⟩ := angular_height_all_frequency_cutoff_mass ℓ
    (γ := γ) (ι := ι) hpub hHuxley hperiod hMV hC hc hc₁ hR hGI hGQ k
  refine ⟨η,σ,hη,hη₁,hσ,?_⟩
  intro L W hL hW hlo hhi
  obtain ⟨Cm,Tm,m,hCm,hmass⟩ := hmass L W hL hW hlo hhi
  obtain ⟨Ce,b,hCe,henv⟩ := logarithmic_full_height_envelope hR hW hlo hhi
  obtain ⟨D₀,D₁₂,hD₀,hD₁₂,hwindow⟩ := arithmeticMellin_signed_height_window M hM V hV hV' q 12
  have hlogevent := exclusion_log_absorption (c := 1) (d := 0) (ε := 1)
    (C := 36*Ce*D₁₂) (by norm_num) (by norm_num) (by positivity) (b+k) 0
  obtain ⟨L₀,hL₀⟩ := eventually_atTop.mp ((eventually_ge_atTop Tm).and
    ((eventually_const_mul_rpow_le (by norm_num : (7/20:ℝ) < 9/25) 5).and hlogevent))
  refine ⟨Cm*D₀+1,L₀,m,by positivity,?_⟩
  intro r X B H e u T ρ ε hL₀' hprod hX hB hBL hH he heN hT hThi hu hρ hε
  obtain ⟨hTm,hheight,hlog⟩ := hL₀ (L r) hL₀'
  have hLp : 0 < L r := zero_lt_one.trans_le (hL r)
  have hz : 0 < 1+Real.log (L r) := by linarith [Real.log_nonneg (hL r)]
  have hTp : 0 < T := (pow_pos hz m).trans_le hT
  let S := (L r)^(1/4:ℝ)
  let G := fullStructuredHeightMass R H 1 e ℓ 0 (W r) X
  let Bl := Cm*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^k
  let E := 36*Ce*D₁₂
  have hXone : ∀ i, 1 ≤ X i := fun i =>
    (Real.one_le_rpow (by linarith [hL r] : 1 ≤ 2*L r) hc.le).trans (hX i).le
  have hSone : 1 ≤ S := Real.one_le_rpow (hL r) (by norm_num)
  have hB₂ : B ≤ (L r)^2 := by
    apply hBL.trans
    rw [← Real.rpow_natCast (L r) 2]
    exact Real.rpow_le_rpow_of_exponent_le (hL r) (by norm_num; linarith)
  have hcard : (H.card:ℝ) ≤ 18*(L r)^2 := by
    have hsub : H ⊆ nonzeroNormBall B := fun h hh =>
      mem_nonzeroNormBall.mpr ⟨(hH h hh).2,(hH h hh).1⟩
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
      ((nonzeroNormBall_card_le (zero_le_one.trans hB)).trans (by gcongr))
  have hgC : ∀ t, ‖G t‖ ≤ 18*Ce*(L r)^4*(1+Real.log (L r))^b := by
    intro t
    rw [Real.norm_eq_abs,abs_of_nonneg (fullStructuredHeightMass_nonneg R H 1 e ℓ 0 (W r) X t)]
    apply (henv r X (hL r) hXone hprod H 1 e ℓ 0 t).trans
    calc
      _ ≤ Ce*(18*(L r)^2)*(L r)^2*(1+Real.log (L r))^b := by gcongr
      _ = _ := by ring
  have hsmall : ∀ s : ℝ, ‖s‖ ≤ S → dyadicHeightMean (fun t => G (t+u+s)) T ≤ Bl := by
    intro s hs
    have hwin : 1+2*T+|u+s| ≤ (L r)^(9/25:ℝ) := by
      rw [Real.norm_eq_abs] at hs
      have ha := abs_add_le u s
      calc
        _ ≤ 5*(L r)^(7/20:ℝ) := by
          have hsmallS : S ≤ (L r)^(7/20:ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (hL r) (by norm_num)
          linarith
        _ ≤ _ := hheight
    have hm := hmass r X B H e (u+s) T hTm hprod hX hB hBL hH he heN hT hwin
    change dyadicHeightMean (fun t => ∑ h ∈ H,
      ‖fullStructuredAngularSum R h 1 e ℓ (t+(u+s)) (W r) X‖^2) T ≤ _ at hm
    change dyadicHeightMean (fun t => ∑ h ∈ H,
      ‖fullStructuredAngularSum R h 1 e ℓ ((t+u+s)+0) (W r) X‖^2) T ≤ _
    simpa only [add_zero,add_assoc] using hm
  have hi := hwindow ρ hρ G (continuous_fullStructuredHeightMass R H 1 e ℓ 0 (W r) X)
    (18*Ce*(L r)^4*(1+Real.log (L r))^b) Bl S T u ε hε
    (by positivity) (by dsimp [Bl]; positivity) (zero_lt_one.trans_le hSone) hTp hgC hsmall
  have hl : E*(1+Real.log (L r))^(b+k) ≤ L r := by
    have hh := hlog (L r) 1 (by norm_num) (by simp) (by simp)
    simpa only [Real.one_rpow,one_mul,mul_one,pow_zero,div_one,E] using hh
  have htail : (2*(18*Ce*(L r)^4*(1+Real.log (L r))^b))/S^12*D₁₂ ≤
      (L r)^2/(1+Real.log (L r))^k := by
    convert polynomial_mellin_tail_absorb hLp hz b k hl using 1
    dsimp only [S,E]
    ring
  have hbase : (L r)^2/(1+Real.log (L r))^k ≤
      (L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^k :=
    div_le_div_of_nonneg_right (le_mul_of_one_le_right (sq_nonneg _)
      (Real.one_le_rpow hB (by norm_num))) (pow_nonneg hz.le k)
  apply hi.trans
  apply (add_le_add le_rfl (htail.trans hbase)).trans_eq
  dsimp only [Bl]
  ring

end CubicFirstMoment

end

end OAI
