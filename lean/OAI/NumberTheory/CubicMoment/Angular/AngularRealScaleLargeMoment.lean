import OAI.NumberTheory.CubicMoment.Estimates.RealScaleLargeMoment
import OAI.NumberTheory.CubicMoment.Angular.AngularLargeConductorMoment

namespace OAI

/-! The large-conductor estimate in the actual real dyadic scales.
The exponents are constructed from logarithms, not supplied as extra data. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_large_conductor_real_scales (hpub : PrimitiveAngularHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {c R κ : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1) (hR : 1 ≤ R) (hκ : 0 < κ)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) :
    ∃ η σ C ν : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < σ ∧ 0 < C ∧ 0 < ν ∧
    ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
      LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → (∀ r i x, R < x → W r i x = 0) →
    ∃ T₀ : ℝ, ∀ (r : γ) (X : ι → ℝ) (U V : ℝ) (v e : Eisenstein) (u : ℝ)
      (Ram S T J H : Finset Eisenstein), T₀ ≤ L r →
      (∏ i, X i) = L r → (∀ i, (2*L r)^c < X i) →
      1 ≤ U → 1 ≤ V → U*V^2 ≤ (L r)^(1+η) → (L r)^κ ≤ U*V^2 →
      v ≠ 0 → e ≠ 0 → norm v ≤ (L r)^σ → norm e ≤ (L r)^σ →
      1+|u| ≤ (L r)^(9/25:ℝ) →
      (∀ a ∈ Ram, a ≠ 0 ∧ norm a ≤ (L r)^σ) →
      (∀ j ∈ J, j ≠ 0 ∧ norm j^3*(U*V^2) ≤ (L r)^(1+η)) →
      (∀ s ∈ S, gramDyad U s) → (∀ t ∈ T, gramDyad V t) →
      H ⊆ coprimeResidualSupport Ram J (coprimePairs S T) →
      (∑ h ∈ H, ‖fullStructuredAngularPrimeSum ℓ R h 1 v e u (W r) X‖^2) ≤
        C*(Ram.card:ℝ)*J.card*(L r)^2*(U*V^2)^(1/3:ℝ)*(L r)^(-ν) := by
  obtain ⟨η,σ,C,ν,hη,hη₁,hσ,hC,hν,hbound⟩ :=
    angular_large_conductor_structured_moment ℓ (γ := γ) (ι := ι) hpub hHuxley hperiod hc hc₁ hR hκ hGI hGQ
  refine ⟨η,σ,C,ν,hη,hη₁,hσ,hC,hν,?_⟩
  intro L W hL hW hlo hhi
  obtain ⟨T₀,hbound⟩ := hbound L W hL hW hlo hhi
  refine ⟨max T₀ 2,?_⟩
  intro r X U V v e u Ram S T J H hT₀ hprod hX hU hV hsize hlarge hv he hvN heN hu hRam hJ hS hT hH
  have hLgt : 1 < L r := by linarith [le_trans (le_max_right T₀ 2) hT₀]
  let p := momentScaleExponent (L r) U
  let q := momentScaleExponent (L r) V
  have hp : (L r)^p = U := rpow_momentScaleExponent hLgt (zero_lt_one.trans_le hU)
  have hq : (L r)^q = V := rpow_momentScaleExponent hLgt (zero_lt_one.trans_le hV)
  have hD : (L r)^(p+2*q) = U*V^2 := by
    rw [rpow_conductor_exponent (zero_lt_one.trans hLgt),hp,hq]
  have hsize' : p+2*q ≤ 1+η := (Real.rpow_le_rpow_left_iff hLgt).mp (by simpa only [hD] using hsize)
  have hlarge' : κ ≤ p+2*q := (Real.rpow_le_rpow_left_iff hLgt).mp (by simpa only [hD] using hlarge)
  have hh := hbound r X p q v e u Ram S T J H ((le_max_left _ _).trans hT₀)
    hprod hX (momentScaleExponent_nonneg hLgt hU) (momentScaleExponent_nonneg hLgt hV)
    hsize' hlarge' hv he hvN heN hu hRam
    (by simpa only [hp,hq] using hJ) (by simpa only [hp] using hS)
    (by simpa only [hq] using hT) hH
  simpa only [hp,hq] using hh

end CubicFirstMoment

end

end OAI
