import OAI.NumberTheory.CubicMoment.Angular.AngularExceptionalStructuredMoment
import OAI.NumberTheory.CubicMoment.Angular.AngularFullPrimeConvolution

namespace OAI

/-! The exceptional moment estimate for the literal, untruncated ordered
prime convolution. The finite output partition is chosen inside the proof. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_full_exceptional_structured_moment (hpub : PrimitiveAngularHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {c R : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1) (hR : 1 ≤ R)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) :
    ∃ ρ ε : ℝ, 0 < ρ ∧ 0 < ε ∧
    ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
      LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → (∀ r i x, R < x → W r i x = 0) →
    ∃ T : ℝ, ∀ (r : γ) (X : ι → ℝ) (v e : Eisenstein) (u p q : ℝ)
      (P : Finset (Eisenstein × Eisenstein)), T ≤ L r →
      (∏ i, X i) = L r → (∀ i, (2*L r)^c < X i) →
      v ≠ 0 → e ≠ 0 → norm v ≤ (L r)^ρ → norm e ≤ (L r)^ρ →
      1+|u| ≤ (L r)^(9/25:ℝ) →
      (∀ z ∈ P, gramDyad ((L r)^p) z.1 ∧ gramDyad ((L r)^q) z.2 ∧ IsCoprime z.1 z.2) →
      ((|p-1| ≤ ρ ∧ 0 ≤ q ∧ q ≤ ρ) ∨ (|p-1/3| ≤ ρ ∧ |q-1/3| ≤ ρ)) →
      (∑ z ∈ P, ‖fullStructuredAngularPrimeSum ℓ R z.1 z.2 v e u (W r) X‖^2) ≤
        (L r)^(7/3-ε) := by
  obtain ⟨J,hJ⟩ := pow_unbounded_of_one_lt (2*R^(Fintype.card ι))
    (by norm_num : (1:ℝ) < 4/3)
  obtain ⟨ρ,ε,hρ,hε,hraw⟩ := angular_exceptional_structured_moment ℓ (γ := γ) (ι := ι)
    hpub hHuxley hperiod hc hc₁ hR J hJ.le hGI hGQ
  refine ⟨ρ,ε,hρ,hε,?_⟩
  intro L W hL hW hlo hhi
  obtain ⟨T,hbound⟩ := hraw L W hL hW hlo hhi
  refine ⟨T,?_⟩
  intro r X v e u p q P hT hprod hXlo hv he hvL heL hu hP hcase
  have hXone : ∀ i, 1 ≤ X i := fun i => (Real.one_le_rpow
    (show 1 ≤ 2*L r by linarith [hL r]) hc.le).trans (hXlo i).le
  have hXhi : ∀ i, X i ≤ L r := fun i => by
    simpa only [hprod] using coordinate_le_product X hXone i
  have hb := hbound r X v e u p q P hT hprod hXlo hXhi hv he hvL heL
    (by linarith : |u| ≤ (L r)^(9/25:ℝ)) hP hcase
  have heq : (∑ z ∈ P, ‖fullStructuredAngularPrimeSum ℓ R z.1 z.2 v e u (W r) X‖^2) =
      ∑ z ∈ P, ‖structuredAngularPrimeSum ℓ z.1 z.2 v e u (W r) X (((4/3:ℝ)^J/2)*L r)‖^2 := by
    apply Finset.sum_congr rfl
    intro z hz
    rw [fullStructuredAngularPrimeSum_partition_cutoff ℓ hR J hJ.le z.1 z.2 v e u (W r) X hXone (hhi r),hprod]
  exact heq.trans_le hb

end CubicFirstMoment

end

end OAI
