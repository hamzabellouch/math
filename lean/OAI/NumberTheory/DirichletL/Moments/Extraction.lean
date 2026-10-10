import OAI.NumberTheory.DirichletL.Moments.Rectangle
import OAI.NumberTheory.DirichletL.Moments.Support

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentExtraction
open CenteredMomentRectangle CenteredMomentPrimary CenteredMomentTwist

theorem idealRectangle_extract (W₁ W₂ : ℝ → ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ I J : Ideal O) :
    idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁ * I) (B₂ * J) =
      idealRectangle W₁ W₂
        (X₁ / Ideal.absNorm B₁) (X₂ / Ideal.absNorm B₂)
        (Y₁ / Ideal.absNorm B₁) (Y₂ / Ideal.absNorm B₂) I J := by
  simp only [idealRectangle, map_mul, Nat.cast_mul, div_div_eq_mul_div]
  congr 2 <;> congr 1 <;> ring

theorem extracted_rectangle_coefficient (c : O)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (P B₁ B₂ I J : Ideal O) :
    idealWeight c χ R t (P * (B₁ * I) * (B₂ * J)) *
        idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁ * I) (B₂ * J) =
      idealWeight c χ R t (P * B₁ * B₂) *
        (idealWeight c χ R t (I * J) *
          idealRectangle W₁ W₂
            (X₁ / Ideal.absNorm B₁) (X₂ / Ideal.absNorm B₂)
            (Y₁ / Ideal.absNorm B₁) (Y₂ / Ideal.absNorm B₂) I J) := by
  rw [idealRectangle_extract]
  simp only [idealWeight_mul]
  ring

theorem extracted_rectangle_sum (c : O)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (P B₁ B₂ : Ideal O) :
    (∑' I : Ideal O, ∑' J : Ideal O,
      idealWeight c χ R t (P * (B₁ * I) * (B₂ * J)) *
        idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁ * I) (B₂ * J)) =
      idealWeight c χ R t (P * B₁ * B₂) *
        ∑' I : Ideal O, ∑' J : Ideal O,
          idealWeight c χ R t (I * J) * idealRectangle W₁ W₂
            (X₁ / Ideal.absNorm B₁) (X₂ / Ideal.absNorm B₂)
            (Y₁ / Ideal.absNorm B₁) (Y₂ / Ideal.absNorm B₂) I J := by
  simp_rw [extracted_rectangle_coefficient, tsum_mul_left]

theorem extracted_product_scale (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ : Ideal O)
    (hX : X₁ * X₂ = T) (hY : Y₁ * Y₂ = T) :
    (X₁ / Ideal.absNorm B₁) * (X₂ / Ideal.absNorm B₂) =
      T / (Ideal.absNorm B₁ * Ideal.absNorm B₂ : ℝ) ∧
    (Y₁ / Ideal.absNorm B₁) * (Y₂ / Ideal.absNorm B₂) =
      T / (Ideal.absNorm B₁ * Ideal.absNorm B₂ : ℝ) := by
  simp only [div_mul_div_comm, hX, hY, and_self]

theorem idealWeight_norm_le_one (c : O) (hc : c ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (I : Ideal O) (hI : I ≠ 0) : ‖idealWeight c χ R t I‖ ≤ 1 := by
  have hnorm : (0 : ℝ) < Ideal.absNorm I := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hpow := norm_real_imaginary_power (Ideal.absNorm I : ℝ) t hnorm
  norm_cast at hpow
  simp only [idealWeight, norm_mul, hpow, mul_one]
  by_cases hcop : IsCoprime I R
  · simpa only [hcop, ite_true, norm_one, one_mul] using primaryIdealCharacter_norm_le_one c hc χ I
  · simp only [hcop, ite_false, norm_zero, zero_mul, zero_le_one]

theorem normalized_extracted_rectangle_estimate
    (c : O) (hc : c ≠ 0) (h3 : (3 : O) ∣ c)
    [Nontrivial (O ⧸ Ideal.span {c})] (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (a₁ b₁ a₂ b₂ ε B : ℝ) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ K : ℕ, ∀ W₁ W₂ : ℝ → ℂ,
      ∀ _hs₁ : Function.support W₁ ⊆ Set.Icc a₁ b₁,
      ∀ _hs₂ : Function.support W₂ ⊆ Set.Icc a₂ b₂,
      ∀ _hW₁ : ContDiff ℝ ∞ W₁, ∀ _hW₂ : ContDiff ℝ ∞ W₂,
      ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z →
      ∀ R : Ideal O, R ≠ 0 → (Ideal.absNorm R : ℝ) ≤ Z ^ B →
      ∀ P B₁ B₂ : Ideal O, P ≠ 0 → B₁ ≠ 0 → B₂ ≠ 0 →
      ∀ t X₁ X₂ Y₁ Y₂ T L : ℝ, 0 < L →
      L ≤ X₁ / Ideal.absNorm B₁ → L ≤ X₂ / Ideal.absNorm B₂ →
      L ≤ Y₁ / Ideal.absNorm B₁ → L ≤ Y₂ / Ideal.absNorm B₂ →
      X₁ * X₂ = T → Y₁ * Y₂ = T →
      let T' := T / (Ideal.absNorm B₁ * Ideal.absNorm B₂ : ℝ)
      ‖(Real.sqrt T' : ℂ)⁻¹ *
        (∑' I : Ideal O, ∑' J : Ideal O,
          idealWeight c χ R t (P * (B₁ * I) * (B₂ * J)) *
            idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁ * I) (B₂ * J))‖ ≤
        C * Z ^ ε * (1 + ‖t‖) ^ K * (Real.sqrt T' / L) := by
  obtain ⟨K, hK⟩ := CenteredMomentHeight.normalized_masked_rectangle_estimate
    c hc h3 χ a₁ b₁ a₂ b₂ ε B ha₁ ha₂ hb₁ hb₂ hε hB
  refine ⟨K, ?_⟩
  intro W₁ W₂ hs₁ hs₂ hW₁ hW₂
  obtain ⟨C, hC, hbound⟩ := hK W₁ W₂ hs₁ hs₂ hW₁ hW₂
  refine ⟨C, hC, ?_⟩
  intro Z hZ R hR hnorm P B₁ B₂ hP hB₁ hB₂ t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  dsimp only
  obtain ⟨heqX, heqY⟩ := extracted_product_scale X₁ X₂ Y₁ Y₂ T B₁ B₂ hpX hpY
  have hraw := hbound Z hZ R hR hnorm t
    (X₁ / Ideal.absNorm B₁) (X₂ / Ideal.absNorm B₂)
    (Y₁ / Ideal.absNorm B₁) (Y₂ / Ideal.absNorm B₂)
    (T / (Ideal.absNorm B₁ * Ideal.absNorm B₂ : ℝ)) L hL hX₁ hX₂ hY₁ hY₂ heqX heqY
  rw [extracted_rectangle_sum, actual_rectangle_sum c χ R t W₁ W₂ b₁ b₂
    (X₁ / Ideal.absNorm B₁) (X₂ / Ideal.absNorm B₂)
    (Y₁ / Ideal.absNorm B₁) (Y₂ / Ideal.absNorm B₂)
    (fun x hx => (hs₁ hx).2) (fun x hx => (hs₂ hx).2)
    (lt_of_lt_of_le hL hX₁) (lt_of_lt_of_le hL hX₂)
    (lt_of_lt_of_le hL hY₁) (lt_of_lt_of_le hL hY₂)]
  have hw := idealWeight_norm_le_one c hc χ R t (P * B₁ * B₂)
    (mul_ne_zero (mul_ne_zero hP hB₁) hB₂)
  rw [mul_left_comm, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hw).trans hraw

theorem centered_slot_allocation {ι : Type*} (T : Finset ι)
    (p : ι → Ideal O) (ν : ι → ℂ) (S : Finset (Ideal O))
    (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ I J : Ideal O) :
    let F := T.filter (fun i => p i ∈ S)
    let L := T.filter (fun i => p i ∉ S)
    (∏ i ∈ T, ν i) *
      (idealWeight c χ R t ((∏ i ∈ T, p i) * (B₁ * I) * (B₂ * J)) *
        idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁ * I) (B₂ * J)) =
      ((∏ i ∈ F, ν i) * idealWeight c χ R t ((∏ i ∈ F, p i) * B₁ * B₂)) *
        ((∏ i ∈ L, ν i) *
          (idealWeight c χ R t ((∏ i ∈ L, p i) * I * J) *
            idealRectangle W₁ W₂
              (X₁ / Ideal.absNorm B₁) (X₂ / Ideal.absNorm B₂)
              (Y₁ / Ideal.absNorm B₁) (Y₂ / Ideal.absNorm B₂) I J)) := by
  dsimp only
  rw [← Finset.prod_filter_mul_prod_filter_not T (fun i => p i ∈ S) ν,
    ← Finset.prod_filter_mul_prod_filter_not T (fun i => p i ∈ S) p,
    idealRectangle_extract]
  simp only [idealWeight_mul]
  ring

theorem prime_slot_allocation {ι : Type*} (T : Finset ι)
    (p : ι → Ideal O) (hp : ∀ i ∈ T, Prime (p i)) (S : Finset (Ideal O)) :
    CenteredMomentSupport.supportExtract (∏ i ∈ T, p i) S =
        ∏ i ∈ T.filter (fun i => p i ∈ S), p i ∧
      CenteredMomentSupport.supportResidual (∏ i ∈ T, p i) S =
        ∏ i ∈ T.filter (fun i => p i ∉ S), p i := by
  rw [CenteredMomentSupport.supportExtract_prod T p (fun i hi => (hp i hi).ne_zero) S,
    CenteredMomentSupport.supportResidual_prod T p (fun i hi => (hp i hi).ne_zero) S]
  constructor
  · rw [Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro i hi
    exact CenteredMomentSupport.supportExtract_prime (p i) (hp i hi) S
  · rw [Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro i hi
    rw [CenteredMomentSupport.supportResidual_prime (p i) (hp i hi) S]
    split_ifs <;> rfl

end SevenEighths.CenteredMomentExtraction
end

end OAI
