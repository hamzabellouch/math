import OAI.NumberTheory.CubicMoment.Angular.AngularLargeCoreMellinIntegral
import OAI.NumberTheory.CubicMoment.Angular.AngularLowCoreMonotone
import OAI.NumberTheory.CubicMoment.Estimates.HeightMassPartition

namespace OAI

/-! All finite noncube frequencies, over the full Mellin line. The
low-core and large-core arguments are now combined without truncating
or modifying the original independent prime coefficients. -/
noncomputable section
open scoped BigOperators ContDiff
open Set Filter MeasureTheory
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem angular_noncube_mellin_integral_saving (hSW : AngularKummerPrimeExplicitEstimate) (hℓ : ℓ ≠ 0)
    (hpub : PrimitiveAngularHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C c R : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hc : 0 < c) (hc₁ : c ≤ 1) (hR : 1 ≤ R)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
    (M : ℝ) (hM : 0 < M) (V : ℝ → ℂ) (hV : HasCompactSupport V)
    (hV' : ContDiff ℝ ∞ V) (k U q : ℕ) :
    ∃ η σ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < σ ∧
    ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
      LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → (∀ r i x, R < x → W r i x = 0) →
    ∃ K T₀ : ℝ, 0 < K ∧ ∀ (r : γ) (X : ι → ℝ) (B : ℝ)
      (H : Finset Eisenstein) (e : Eisenstein) (u ρ : ℝ), T₀ ≤ L r →
      (∏ i, X i) = L r → (∀ i, (2*L r)^c < X i) →
      1 ≤ B → B ≤ (L r)^(1+η) →
      (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B ∧ ¬∃ z : Eisenstein, z^3 = h) →
      e ≠ 0 → norm e ≤ (L r)^σ → |u| ≤ (1+Real.log (L r))^U → 0 ≤ ρ →
      (1+ρ)^q*(∫ t : ℝ, ‖arithmeticMellinCoefficient M hM V hV hV' ρ t‖*
        fullStructuredHeightMass R H 1 e ℓ u (W r) X t) ≤
          K*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^k := by
  obtain ⟨η,σ,hη,hη₁,hσ,hlarge⟩ := angular_large_core_mellin_integral_saving ℓ
    (γ := γ) (ι := ι) hpub hHuxley hperiod hc hc₁ hR hGI hGQ M hM V hV hV' k q
  refine ⟨η,σ,hη,hη₁,hσ,?_⟩
  intro L W hL hW hlo hhi
  obtain ⟨Kg,Tg,a,hKg,hlarge⟩ := hlarge L W hL hW hlo hhi
  obtain ⟨Kl,Tl,hKl,hlow⟩ := angular_low_core_mellin_integral_all_exponents ℓ hSW hℓ hMV hC hR hc
    hσ.le (by norm_num : (0:ℝ) ≤ 1) hW hlo hhi M hM V hV hV' a k U q
  have hheight := exclusion_log_absorption (c := 1/4) (d := 0) (ε := 1) (C := 1)
    (by norm_num) (by norm_num) (by norm_num) U 0
  obtain ⟨T₀,hT₀⟩ := eventually_atTop.mp ((eventually_ge_atTop Tg).and
    ((eventually_ge_atTop Tl).and hheight))
  refine ⟨Kl+Kg,T₀,by positivity,?_⟩
  intro r X B H e u ρ hT hprod hX hB hBL hH he heN hu hρ
  obtain ⟨hTg,hTl,hheight⟩ := hT₀ (L r) hT
  let J := B^(1/3:ℝ)
  let P := fun h : Eisenstein => h ∈ lowNoncubeSupport ((Real.log (L r))^a) J
  have hLp : 0 < L r := zero_lt_one.trans_le (hL r)
  have hB2 : B ≤ (L r)^2 := by
    apply hBL.trans
    rw [← Real.rpow_natCast (L r) 2]
    exact Real.rpow_le_rpow_of_exponent_le (hL r) (by norm_num; linarith)
  have hJ : 0 ≤ J := Real.rpow_nonneg (zero_le_one.trans hB) _
  have hJL : J ≤ (L r)^(1:ℝ) := by
    simpa only [Real.rpow_one] using cube_cutoff_le_length (zero_le_one.trans hB) (hL r) hB2
  have hrough : ∀ i, (L r)^c ≤ X i := by
    intro i
    exact (Real.rpow_le_rpow hLp.le (by linarith) hc.le).trans (hX i).le
  have hulo : |u| ≤ (L r)^(1/4:ℝ) := by
    have hh := hheight ((L r)^(1/4:ℝ)) 1 (by norm_num) (by simp) le_rfl
    simp only [Real.one_rpow,one_mul,pow_zero,div_one] at hh
    exact hu.trans hh
  have hl := hlow r X J (H.filter P) hTl hprod hrough hJ hJL
    (fun h hh => (Finset.mem_filter.mp hh).2) e u ρ he heN hu hρ
  have hg := hlarge r X B (H.filter (fun h => ¬P h)) e u ρ hTg hprod hX hB hBL
    (fun h hh => ⟨(hH h (Finset.mem_filter.mp hh).1).1,
      (hH h (Finset.mem_filter.mp hh).1).2.1,
      (hH h (Finset.mem_filter.mp hh).1).2.2,(Finset.mem_filter.mp hh).2⟩) he heN hulo hρ
  rw [weighted_height_mass_partition
    (arithmeticMellinCoefficient_integrable M hM V hV hV' ρ).norm R H P 1 e ℓ u (W r) X,mul_add]
  convert add_le_add hl hg using 1
  · congr 4
    all_goals
      funext t
      congr 2
      apply Finset.filter_congr_decidable
  · dsimp only [J]
    ring

end CubicFirstMoment

end

end OAI
