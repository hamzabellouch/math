import OAI.NumberTheory.CubicMoment.Angular.AngularFullPrimeConvolution
import OAI.NumberTheory.CubicMoment.Angular.AngularLargeCorePolynomialHeight
import OAI.NumberTheory.CubicMoment.Estimates.FullStructuredHeightEnvelope
import OAI.NumberTheory.CubicMoment.Estimates.MellinWindowIntegral

namespace OAI

/-! The large-core mass over all Mellin heights. The polynomial-height
sieve controls the window; the literal coefficient envelope and the
kernel's twelfth moment control the complement. -/
noncomputable section
open scoped BigOperators ContDiff
open Set Filter MeasureTheory
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_large_core_mellin_integral_saving (hpub : PrimitiveAngularHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {c R : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1) (hR : 1 ≤ R)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
    (M : ℝ) (hM : 0 < M) (V : ℝ → ℂ) (hV : HasCompactSupport V)
    (hV' : ContDiff ℝ ∞ V) (k q : ℕ) :
    ∃ η σ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < σ ∧
    ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
      LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → (∀ r i x, R < x → W r i x = 0) →
    ∃ (K T₀ : ℝ) (a : ℕ), 0 < K ∧ ∀ (r : γ) (X : ι → ℝ) (B : ℝ)
      (H : Finset Eisenstein) (e : Eisenstein) (u ρ : ℝ), T₀ ≤ L r →
      (∏ i, X i) = L r → (∀ i, (2*L r)^c < X i) →
      1 ≤ B → B ≤ (L r)^(1+η) →
      (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B ∧ (¬∃ z : Eisenstein, z^3 = h) ∧
        h ∉ lowNoncubeSupport ((Real.log (L r))^a) (B^(1/3:ℝ))) →
      e ≠ 0 → norm e ≤ (L r)^σ → |u| ≤ (L r)^(1/4:ℝ) → 0 ≤ ρ →
      (1+ρ)^q*(∫ t : ℝ, ‖arithmeticMellinCoefficient M hM V hV hV' ρ t‖*
        fullStructuredHeightMass R H 1 e ℓ u (W r) X t) ≤
          K*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^k := by
  obtain ⟨η,σ,hη,hη₁,hσ,hlarge⟩ := angular_large_core_cutoff_polynomial_height ℓ
    (γ := γ) (ι := ι) hpub hHuxley hperiod hc hc₁ hR hGI hGQ k
  refine ⟨η,σ,hη,hη₁,hσ,?_⟩
  intro L W hL hW hlo hhi
  obtain ⟨Cl,Tl,a,hCl,hlarge⟩ := hlarge L W hL hW hlo hhi
  obtain ⟨Ce,b,hCe,henv⟩ := logarithmic_full_height_envelope hR hW hlo hhi
  obtain ⟨D₀,D₁₂,hD₀,hD₁₂,hwindow⟩ := arithmeticMellin_bounded_window M hM V hV hV' q 12
  have hlogevent := exclusion_log_absorption (c := 1) (d := 0) (ε := 1) (C := 18*Ce*D₁₂)
    (by norm_num) (by norm_num) (by positivity) (b+k) 0
  obtain ⟨T₀,hT₀⟩ := eventually_atTop.mp ((eventually_ge_atTop Tl).and
    ((eventually_const_mul_rpow_le (by norm_num : (1/4:ℝ) < 9/25) 3).and hlogevent))
  refine ⟨Cl*D₀+1,T₀,a,by positivity,?_⟩
  intro r X B H e u ρ hT hprod hX hB hBL hH he heN hu hρ
  obtain ⟨hTl,hheight,hlog⟩ := hT₀ (L r) hT
  have hLp : 0 < L r := zero_lt_one.trans_le (hL r)
  have hz : 0 < 1+Real.log (L r) := by linarith [Real.log_nonneg (hL r)]
  let T := (L r)^(1/4:ℝ)
  let G := fullStructuredHeightMass R H 1 e ℓ u (W r) X
  let Bl := Cl*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^k
  let E := 18*Ce*D₁₂
  have hX1 : ∀ i, 1 ≤ X i := fun i =>
    (Real.one_le_rpow (by linarith [hL r] : (1:ℝ) ≤ 2*L r) hc.le).trans (hX i).le
  have hT1 : 1 ≤ T := Real.one_le_rpow (hL r) (by norm_num)
  have hB2 : B ≤ (L r)^2 := by
    apply hBL.trans
    rw [← Real.rpow_natCast (L r) 2]
    exact Real.rpow_le_rpow_of_exponent_le (hL r) (by norm_num; linarith)
  have hcard : (H.card:ℝ) ≤ 18*(L r)^2 := by
    have hsub : H ⊆ nonzeroNormBall B := fun h hh =>
      mem_nonzeroNormBall.mpr ⟨(hH h hh).2.1,(hH h hh).1⟩
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
      ((nonzeroNormBall_card_le (zero_le_one.trans hB)).trans (by gcongr))
  have hgC : ∀ t, G t ≤ 18*Ce*(L r)^4*(1+Real.log (L r))^b := by
    intro t
    apply (henv r X (hL r) hX1 hprod H 1 e ℓ u t).trans
    calc
      _ ≤ Ce*(18*(L r)^2)*(L r)^2*(1+Real.log (L r))^b := by gcongr
      _ = _ := by ring
  have hsmall : ∀ t : ℝ, ‖t‖ ≤ T → G t ≤ Bl := by
    intro t ht
    have hs : 1+|t+u| ≤ (L r)^(9/25:ℝ) := by
      have ha := abs_add_le t u
      rw [Real.norm_eq_abs] at ht
      calc
        _ ≤ 1+(|t|+|u|) := by linarith
        _ ≤ 3*T := by dsimp only [T] at *; linarith
        _ ≤ _ := hheight
    simpa only [G,Bl,fullStructuredHeightMass,←fullStructuredAngularPrimeSum_eq_existing ℓ] using
      hlarge r X B H e (t+u) hTl hprod hX hB hBL hH he heN hs
  have hi := hwindow ρ hρ G (continuous_fullStructuredHeightMass R H 1 e ℓ u (W r) X)
    (fullStructuredHeightMass_nonneg R H 1 e ℓ u (W r) X) Bl
    (18*Ce*(L r)^4*(1+Real.log (L r))^b) T (by dsimp [Bl]; positivity)
    (by positivity) (zero_lt_one.trans_le hT1) hgC hsmall
  have hl : E*(1+Real.log (L r))^(b+k) ≤ L r := by
    have hh := hlog (L r) 1 (by norm_num) (by simp) (by simp)
    simpa only [Real.one_rpow,one_mul,mul_one,pow_zero,div_one,E] using hh
  have htail : (18*Ce*(L r)^4*(1+Real.log (L r))^b)/T^12*D₁₂ ≤
      (L r)^2/(1+Real.log (L r))^k := by
    convert polynomial_mellin_tail_absorb hLp hz b k hl using 1
    dsimp only [T,E]
    ring
  have hbroot : 1 ≤ B^(1/3:ℝ) := Real.one_le_rpow hB (by norm_num)
  have hbase : (L r)^2/(1+Real.log (L r))^k ≤
      (L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^k :=
    div_le_div_of_nonneg_right (le_mul_of_one_le_right (sq_nonneg _) hbroot) (pow_nonneg hz.le k)
  apply hi.trans
  apply (add_le_add le_rfl (htail.trans hbase)).trans_eq
  dsimp only [Bl]
  ring

end CubicFirstMoment

end

end OAI
