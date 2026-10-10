import OAI.NumberTheory.CubicMoment.Angular.AngularFirstUnweightedStructuredMoment
import OAI.NumberTheory.CubicMoment.Angular.AngularBalancedUnweightedStructuredMoment

namespace OAI

/-! Both exceptional conductor neighborhoods for the original structured
prime sum, with common constants and the actual finite pair set. -/
noncomputable section
open Filter
open scoped BigOperators
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

variable (ℓ : ℤ)

theorem angular_exceptional_structured_moment (hpub : PrimitiveAngularHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {c R : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1) (hR : 1 ≤ R)
    (J : ℕ) (hJ : 2*R^(Fintype.card ι) ≤ (4/3:ℝ)^J)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) :
    ∃ ρ ε : ℝ, 0 < ρ ∧ 0 < ε ∧
    ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
      LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → (∀ r i x, R < x → W r i x = 0) →
    ∃ T : ℝ, ∀ (r : γ) (X : ι → ℝ) (v e : Eisenstein) (u p q : ℝ)
      (P : Finset (Eisenstein × Eisenstein)), T ≤ L r →
      (∏ i, X i) = L r → (∀ i, (2*L r)^c < X i) → (∀ i, X i ≤ L r) →
      v ≠ 0 → e ≠ 0 → norm v ≤ (L r)^ρ → norm e ≤ (L r)^ρ → |u| ≤ (L r)^(9/25:ℝ) →
      (∀ z ∈ P, gramDyad ((L r)^p) z.1 ∧ gramDyad ((L r)^q) z.2 ∧ IsCoprime z.1 z.2) →
      ((|p-1| ≤ ρ ∧ 0 ≤ q ∧ q ≤ ρ) ∨ (|p-1/3| ≤ ρ ∧ |q-1/3| ≤ ρ)) →
      (∑ z ∈ P, ‖structuredAngularPrimeSum ℓ z.1 z.2 v e u (W r) X (((4/3:ℝ)^J/2)*L r)‖^2) ≤
        (L r)^(7/3-ε) := by
  obtain ⟨d₁,hd₁,_,e₁,he₁,hfirst⟩ := angular_first_unweighted_structured_moment ℓ
    (γ := γ) (ι := ι) hpub hperiod hc hc₁ hR J hJ hGI hGQ
  obtain ⟨d₂,hd₂,_,e₂,he₂,hbalanced⟩ := angular_balanced_unweighted_structured_moment ℓ
    (γ := γ) (ι := ι) hpub hHuxley hperiod hc hc₁ hR J hJ hGI hGQ
  let ρ := min d₁ d₂/4
  have hρ : 0 < ρ := div_pos (lt_min hd₁ hd₂) (by norm_num)
  have hρ₁ : ρ < d₁ := by dsimp [ρ]; linarith [min_le_left d₁ d₂]
  have hρ₂ : ρ < d₂ := by dsimp [ρ]; linarith [min_le_right d₁ d₂]
  refine ⟨ρ,min e₁ e₂,hρ,lt_min he₁ he₂,?_⟩
  intro L W hL hW hlo hhi
  obtain ⟨T₁,hF⟩ := hfirst L W hL hW hlo hhi
  obtain ⟨T₂,hB⟩ := hbalanced L W hL hW hlo hhi
  obtain ⟨T₃,hsmall⟩ := eventually_atTop.mp (eventually_const_mul_rpow_le hρ₁ 2)
  obtain ⟨T₄,hupper⟩ := eventually_atTop.mp (eventually_const_mul_rpow_le
    (by linarith : 1/3+ρ < 1/3+d₂) 2)
  refine ⟨max (max T₁ T₂) (max T₃ T₄),?_⟩
  intro r X v e u p q P hT hprod hXlo hXhi hv he hvY heY hu hP hcase
  have hT₁ : T₁ ≤ L r := (le_max_left T₁ T₂).trans ((le_max_left _ _).trans hT)
  have hT₂ : T₂ ≤ L r := (le_max_right T₁ T₂).trans ((le_max_left _ _).trans hT)
  have hT₃ : T₃ ≤ L r := (le_max_left T₃ T₄).trans ((le_max_right _ _).trans hT)
  have hT₄ : T₄ ≤ L r := (le_max_right T₃ T₄).trans ((le_max_right _ _).trans hT)
  have hv₁ := hvY.trans (Real.rpow_le_rpow_of_exponent_le (hL r) hρ₁.le)
  have he₁' := heY.trans (Real.rpow_le_rpow_of_exponent_le (hL r) hρ₁.le)
  have hv₂ := hvY.trans (Real.rpow_le_rpow_of_exponent_le (hL r) hρ₂.le)
  have he₂' := heY.trans (Real.rpow_le_rpow_of_exponent_le (hL r) hρ₂.le)
  rcases hcase with ⟨hp,hqlo,hqhi⟩ | ⟨hp,hq⟩
  · let A := P.image Prod.fst
    let B := P.image Prod.snd
    have hNlo : (L r)^(1-d₁) ≤ (L r)^p :=
      Real.rpow_le_rpow_of_exponent_le (hL r) (by linarith [(abs_le.mp hp).1])
    have hNhi : (L r)^p ≤ (L r)^(1+d₁) :=
      Real.rpow_le_rpow_of_exponent_le (hL r) (by linarith [(abs_le.mp hp).2])
    have hA : ∀ a ∈ A, gramDyad ((L r)^p) a := by
      intro a ha
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp ha
      exact (hP z hz).1
    have hB' : ∀ b ∈ B, primary b ∧ norm b ≤ (L r)^d₁ := by
      intro b hb
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hb
      have hz' := (hP z hz).2.1
      refine ⟨hz'.1,?_⟩
      apply hz'.2.2.2.le.trans
      exact (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (hL r) hqhi) (by norm_num)).trans (hsmall (L r) hT₃)
    have hb := hF r ((L r)^p) X v e u A B hT₁ hNlo hNhi hprod hXlo hXhi
      hv he hv₁ he₁' hu hA hB'
    have hsub : P ⊆ A ×ˢ B := fun z hz => Finset.mem_product.mpr
      ⟨Finset.mem_image_of_mem _ hz,Finset.mem_image_of_mem _ hz⟩
    calc
      _ ≤ ∑ z ∈ A ×ˢ B,
          ‖structuredAngularPrimeSum ℓ z.1 z.2 v e u (W r) X (((4/3:ℝ)^J/2)*L r)‖^2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
      _ = ∑ b ∈ B, ∑ a ∈ A,
          ‖structuredAngularPrimeSum ℓ a b v e u (W r) X (((4/3:ℝ)^J/2)*L r)‖^2 := by
        rw [Finset.sum_product,Finset.sum_comm]
      _ ≤ (L r)^(7/3-e₁) := hb
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (hL r) (by linarith [min_le_left e₁ e₂])
  · have hrows : ∀ z ∈ P, PrimarySquarefreePair z ∧
        norm z.1 ≤ (L r)^(1/3+d₂) ∧ norm z.2 ≤ (L r)^(1/3+d₂) ∧
        (L r)^(1/3-d₂) ≤ norm z.1 := by
      intro z hz
      obtain ⟨hzp,hzq,hcop⟩ := hP z hz
      refine ⟨⟨hzp.1,hzq.1,hzp.2.1,hzq.2.1,hcop⟩,?_,?_,?_⟩
      · apply hzp.2.2.2.le.trans
        exact (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le (hL r) (by linarith [(abs_le.mp hp).2]))
          (by norm_num)).trans (hupper (L r) hT₄)
      · apply hzq.2.2.2.le.trans
        exact (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le (hL r) (by linarith [(abs_le.mp hq).2]))
          (by norm_num)).trans (hupper (L r) hT₄)
      · exact (Real.rpow_le_rpow_of_exponent_le (hL r)
          (by linarith [(abs_le.mp hp).1])).trans hzp.2.2.1
    exact (hB r X v e u P hT₂ hprod hXlo hXhi hv he hv₂ he₂' hu hrows).trans
      (Real.rpow_le_rpow_of_exponent_le (hL r) (by linarith [min_le_right e₁ e₂]))

end CubicFirstMoment

end

end OAI
