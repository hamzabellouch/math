import OAI.NumberTheory.CubicMoment.Angular.AngularCoprimeNoncubeIntegral
import OAI.NumberTheory.CubicMoment.Estimates.FullPrimeMellin
import OAI.NumberTheory.CubicMoment.Estimates.NormCoprimeMellin

namespace OAI

/-! The literal norm-denominator Poisson form on a noncube annulus.
The ambient prime set is constructed from the coefficients' actual support. -/
noncomputable section
open scoped BigOperators ContDiff
open Set Filter MeasureTheory
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem angular_noncube_radial_form_saving (hSW : AngularKummerPrimeExplicitEstimate) (hℓ : ℓ ≠ 0)
    (hpub : PrimitiveAngularHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C c R : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hc : 0 < c) (hc₁ : c ≤ 1) (hR : 1 ≤ R)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (k U q : ℕ) :
    ∃ η σ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < σ ∧
    ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
      LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → (∀ r i x, R < x → W r i x = 0) →
    ∃ K T₀ : ℝ, 0 < K ∧ ∀ (r : γ) (X : ι → ℝ) (B J : ℝ)
      (H : Finset Eisenstein) (e : Eisenstein) (u ρ : ℝ) (phase : Eisenstein → ℂ), T₀ ≤ L r →
      (∏ i, X i) = L r → (∀ i, (2*L r)^c < X i) →
      1 ≤ B → B ≤ (L r)^(1+η) → 0 < J →
      (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B ∧ ¬∃ z : Eisenstein, z^3 = h) →
      (∀ h ∈ H, J ≤ norm h ∧ norm h ≤ 2*J) → (∀ h ∈ H, ‖phase h‖ ≤ 1) →
      e ≠ 0 → norm e ≤ (L r)^σ → |u| ≤ (1+Real.log (L r))^U → 0 ≤ ρ →
      (1+ρ)^q*‖normCoprimeRadialForm (fullSquarefreePrimeSupport R (W r) X e) H
        (fun a => star (angularHeightPrimeCoefficient ℓ R (W r) X a*mellinPhase u (norm a)))
        (fun a => star (angularHeightPrimeCoefficient ℓ R (W r) X a*mellinPhase u (norm a)))
        phase (fun h => norm h/J) (fun a => norm a/L r) V ρ‖ ≤
          K*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^k := by
  let M := primeConvolutionLogRadius R (Fintype.card ι)
  have hM : 0 < M := primeConvolutionLogRadius_pos hR _
  obtain ⟨η,σ,hη,hη₁,hσ,hmass⟩ := angular_coprime_noncube_mellin_integral_saving ℓ
    (γ := γ) (ι := ι) hSW hℓ hpub hHuxley hperiod hMV hC hc hc₁ hR hGI hGQ
    M hM V hV hV' k U q
  refine ⟨η,σ,hη,hη₁,hσ,?_⟩
  intro L W hL hW hlo hhi
  obtain ⟨K,T₀,hK,hmass⟩ := hmass L W hL hW hlo hhi
  refine ⟨K,T₀,hK,?_⟩
  intro r X B J H e u ρ phase hT hprod hX hB hBL hJ hH hHJ hphase he heN hu hρ
  let S := fullSquarefreePrimeSupport R (W r) X e
  let P := S.biUnion primaryPrimeFactors
  have hS : ∀ a ∈ S, primary a ∧ Squarefree a :=
    fun a ha => fullSquarefreePrimeSupport_primary R (W r) X e ha
  have hP : ∀ p ∈ P, primaryPrime p := by
    intro p hp
    obtain ⟨a,ha,hpa⟩ := Finset.mem_biUnion.mp hp
    exact (primaryPrimeFactor_spec (hS a ha).1 hpa).1
  have hSP : ∀ a ∈ S, primaryPrimeFactors a ⊆ P := by
    intro a ha p hp
    exact Finset.mem_biUnion.mpr ⟨a,ha,hp⟩
  have hLp : 0 < L r := zero_lt_one.trans_le (hL r)
  have hXpos : ∀ i, 0 < X i := fun i => lt_of_lt_of_le zero_lt_one
    ((Real.one_le_rpow (by linarith [hL r] : (1:ℝ) ≤ 2*L r) hc.le).trans (hX i).le)
  have hlog := fullPrimeMellin_log_range hR hJ (W r) X hXpos (hlo r) (hhi r) e H hHJ
  rw [hprod] at hlog
  have hn := normCoprimeRadialForm_norm_le_mass M hM S H P hS hP hSP
    (fun a => star (angularHeightPrimeCoefficient ℓ R (W r) X a*mellinPhase u (norm a)))
    (fun a => star (angularHeightPrimeCoefficient ℓ R (W r) X a*mellinPhase u (norm a))) phase hphase
    (fun h => norm h/J) (fun a => norm a/L r)
    (fun h hh => (le_div_iff₀ hJ).mpr (by simpa using (hHJ h hh).1))
    (fun a ha => div_pos (norm_pos_of_ne_zero (primary_ne_zero (hS a ha).1)) hLp)
    hlog V hV hV' hρ
  exact (mul_le_mul_of_nonneg_left hn (by positivity)).trans
    (hmass r X B H P e u ρ (L r) hT hprod hX hB hBL hH hP he heN hu hρ hLp)

end CubicFirstMoment

end

end OAI
