import OAI.NumberTheory.CubicMoment.Estimates.CommonSquarefreePrimeExponents
import OAI.NumberTheory.CubicMoment.Estimates.SmallSecondConductorPowers

namespace OAI

/-! The first exceptional moment with its actual small second conductor. -/
noncomputable section
open Set
open scoped ContDiff BigOperators
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

 theorem first_common_small_second_exponents (hpub : PrimitiveResidueHeckeInput)
    {c : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hposV : tsupport V ⊆ Ioi 0)
    (hsmV : ContDiff ℝ ∞ V) (hVlo : ∀ x, x < 1 → V x = 0) (hVhi : ∀ x, 2 < x → V x = 0)
    (hVnorm : ∀ x, ‖V x‖ ≤ 1)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/10000 ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ (W : γ → ι → ℝ → ℂ), UniformLogWeights (fun z : γ × ι => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → ∃ Y₀ : ℝ,
      ∀ (r : γ) (Y N : ℝ) (X : ι → ℝ) (q : ι → Eisenstein)
      (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ) (P Q : Finset Eisenstein),
      Y₀ ≤ Y → 1 ≤ Real.log Y → Y^(1-δ) ≤ N → N ≤ Y^(1+δ) →
      (∀ i, (2*Y)^c < X i) → (∀ i, X i ≤ Y^2) → (∀ i, q i ≠ 0) →
      (∀ i, ∀ e : Eisensteinˣ, η i (Ideal.Quotient.mk (modulus (q i)) e) = 1) →
      (∀ i, norm (q i) ≤ Y^δ) → (∀ i, |t i| ≤ Y^(721/2000:ℝ)) →
      (∀ a ∈ P, gramDyad N a) → (∀ b ∈ Q, primary b ∧ norm b ≤ Y^δ) →
      (∑ b ∈ Q, ∑ a ∈ P, ‖primarySquarefreePrimeTuple a b q η t (W r) X V Y‖^2) ≤
        Y^(7/3-ε) := by
  obtain ⟨κ,hκ,hκhi,e,he,hfamily⟩ := first_common_squarefree_exponents (γ := γ) (ι := ι)
    hpub hc hc₁ V hV hposV hsmV hVlo hVhi hVnorm hGI hGQ
  let δ := min κ (min (e/4) (1/400000))
  have hδ : 0 < δ := lt_min hκ (lt_min (by positivity) (by norm_num))
  have hδκ : δ ≤ κ := min_le_left _ _
  have hδe : δ ≤ e/4 := (min_le_right _ _).trans (min_le_left _ _)
  have hδsmall : δ ≤ 1/400000 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨T₁,hT₁,habs⟩ := small_second_conductor_absorption he hδ hδe
  refine ⟨δ,hδ,hδκ.trans hκhi,e/2,by positivity,?_⟩
  intro W hW hWlo
  obtain ⟨T₀,hfirst⟩ := hfamily W hW hWlo
  refine ⟨max T₀ T₁,?_⟩
  intro r Y N X q η t P Q hYT hlog hNlo hNhi hXlo hXhi hq hη hqY ht hP hQ
  have hYT₀ : T₀ ≤ Y := (le_max_left _ _).trans hYT
  have hYT₁ : T₁ ≤ Y := (le_max_right _ _).trans hYT
  have hY1 : 1 ≤ Y := hT₁.trans hYT₁
  have hYp : 0 < Y := zero_lt_one.trans_le hY1
  have hNloκ : Y^(1-κ) ≤ N :=
    (Real.rpow_le_rpow_of_exponent_le hY1 (by linarith)).trans hNlo
  have hNhiκ : N ≤ Y^(1+κ) := hNhi.trans
    (Real.rpow_le_rpow_of_exponent_le hY1 (by linarith))
  have hrow (b : Eisenstein) (hb : b ∈ Q) :
      (∑ a ∈ P, ‖primarySquarefreePrimeTuple a b q η t (W r) X V Y‖^2) ≤ Y^(7/3-e) := by
    let ρ := 3*(1*b)
    let ψ := primaryMixedResidueChar 1 b primary_one (hQ b hb).1
    have hr : ρ ≠ 0 := mul_ne_zero (by norm_num) (mul_ne_zero one_ne_zero
      (primary_ne_zero (hQ b hb).1))
    have hu := primaryMixedResidueChar_trivialInfinity primary_one (hQ b hb).1
    have hm := hfirst r Y N X (fun i => q i*ρ)
      (fun i => productResidueChar (η i) ψ) t P hYT₀ hlog hNloκ hNhiκ hXlo hXhi
      (fun i => mul_ne_zero (hq i) hr)
      (fun i u => productResidueChar_units (η i) ψ (hη i) hu u)
      (fun i => small_second_modulus hY1 hδsmall (habs Y hYT₁).1 (hqY i) (hQ b hb).2) ht hP
    convert hm using 1
    apply Finset.sum_congr rfl
    intro a ha
    rw [squarefreePrimeTuple_small_second_conductor a b (hQ b hb).1 q η t (W r) X V Y]
  have hcard : (Q.card:ℝ) ≤ 18*Y^δ := by
    have hsub : Q ⊆ nonzeroNormBall (Y^δ) := fun b hb =>
      mem_nonzeroNormBall.mpr ⟨(hQ b hb).2,primary_ne_zero (hQ b hb).1⟩
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
      (nonzeroNormBall_card_le (Real.rpow_nonneg hYp.le δ))
  calc
    _ ≤ ∑ _b ∈ Q, Y^(7/3-e) := Finset.sum_le_sum hrow
    _ = (Q.card:ℝ)*Y^(7/3-e) := by simp
    _ ≤ 18*Y^δ*Y^(7/3-e) := mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg hYp.le _)
    _ ≤ _ := (habs Y hYT₁).2

end CubicFirstMoment

end

end OAI
