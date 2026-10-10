import OAI.Analysis.FiniteFactor.Sampling.FourierSum

namespace OAI

namespace FiniteFactor
open MeasureTheory Finset
noncomputable section

/-- The finite kernel index form, with total coefficient absolute sum at most H. -/
theorem samplingSmooth_index_expansion (H : ℕ) (E : Set ℝ) (t : ℝ) :
    (samplingSmooth H E t : ℂ) = (H : ℂ)⁻¹ *
      ∑ p ∈ (Finset.range H).product (Finset.range H),
        samplingIntervalCoefficient E ((p.1 : ℤ)-(p.2 : ℤ)) *
          samplingCharacter ((p.1 : ℤ)-(p.2 : ℤ)) t := by
  rw [samplingSmooth_expansion, Finset.product_eq_sprod, sum_product]
  congr 1
  apply sum_congr rfl
  intro r hr
  apply sum_congr rfl
  intro q hq
  exact mul_comm _ _

theorem samplingSmooth_constant_sum (H : ℕ) (E : Set ℝ) :
    (∑ p ∈ (Finset.range H).product (Finset.range H),
      if (p.1 : ℤ)-(p.2 : ℤ) = 0 then
        samplingIntervalCoefficient E ((p.1 : ℤ)-(p.2 : ℤ)) else 0) =
      (H : ℂ)*((unitIntervalMeasure E).toReal : ℂ) := by
  simp [sum_product, sub_eq_zero, -Finset.mem_range, samplingIntervalCoefficient_zero]

/-- Quantitative smoothed rectangle estimate, with the actual joint Fourier
bound as the only dependence assumption. -/
theorem samplingSmooth_pair_error {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ)
    (hX : Measurable X) (hY : Measurable Y) (H : ℕ) (hH : 0 < H)
    (E E' : Set ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hFourier : ∀ v w : ℤ, |v| < (H : ℤ) → |w| < (H : ℤ) →
      (v ≠ 0 ∨ w ≠ 0) →
      ‖∫ θ, samplingCharacter v (X θ)*samplingCharacter w (Y θ) ∂μ‖ ≤ ε) :
    ‖(∫ θ, (samplingSmooth H E (X θ) : ℂ)*(samplingSmooth H E' (Y θ) : ℂ) ∂μ) -
      ((unitIntervalMeasure E).toReal : ℂ)*((unitIntervalMeasure E').toReal : ℂ)‖ ≤
      (H : ℝ)^2*ε := by
  let F := (Finset.range H).product (Finset.range H)
  let v := fun p : ℕ × ℕ => (p.1 : ℤ)-(p.2 : ℤ)
  let A := fun p => samplingIntervalCoefficient E (v p)
  let B := fun p => samplingIntervalCoefficient E' (v p)
  let P := fun t => ∑ p ∈ F, A p*samplingCharacter (v p) t
  let Q := fun t => ∑ p ∈ F, B p*samplingCharacter (v p) t
  have hfreq (p : ℕ × ℕ) (hp : p ∈ F) : |v p| < (H : ℤ) := by
    obtain ⟨hp,hq⟩ := mem_product.mp hp
    have hp' := mem_range.mp hp
    have hq' := mem_range.mp hq
    dsimp [v]
    rw [abs_lt]
    constructor <;> omega
  have hh := samplingFourier_sum_error μ X Y hX hY F F v v A B
    (fun p hp => samplingIntervalCoefficient_norm E (v p))
    (fun p hp => samplingIntervalCoefficient_norm E' (v p)) ε hε
    (fun p hp q hq hn => hFourier (v p) (v q) (hfreq p hp) (hfreq q hq) hn)
  have ha : (∑ p ∈ F, if v p = 0 then A p else 0) =
      (H : ℂ)*((unitIntervalMeasure E).toReal : ℂ) := samplingSmooth_constant_sum H E
  have hb : (∑ p ∈ F, if v p = 0 then B p else 0) =
      (H : ℂ)*((unitIntervalMeasure E').toReal : ℂ) := samplingSmooth_constant_sum H E'
  rw [ha,hb] at hh
  change ‖(∫ θ, P (X θ)*Q (Y θ) ∂μ) - _‖ ≤ _ at hh
  have hmain : (∫ θ, (samplingSmooth H E (X θ) : ℂ)*(samplingSmooth H E' (Y θ) : ℂ) ∂μ) =
      (H : ℂ)⁻¹^2 * ∫ θ, P (X θ)*Q (Y θ) ∂μ := by
    simp_rw [samplingSmooth_index_expansion]
    change (∫ θ, ((H : ℂ)⁻¹*P (X θ))*((H : ℂ)⁻¹*Q (Y θ)) ∂μ) = _
    have he (θ : Ω) : ((H : ℂ)⁻¹*P (X θ))*((H : ℂ)⁻¹*Q (Y θ)) =
        (H : ℂ)⁻¹^2*(P (X θ)*Q (Y θ)) := by ring
    simp_rw [he]
    exact integral_const_mul _ _
  have hHC : (H : ℂ) ≠ 0 := by exact_mod_cast hH.ne'
  have hHR : (H : ℝ) ≠ 0 := by exact_mod_cast hH.ne'
  have hz : (H : ℂ)⁻¹^2*((H : ℂ)*((unitIntervalMeasure E).toReal : ℂ)*
      ((H : ℂ)*((unitIntervalMeasure E').toReal : ℂ))) =
      ((unitIntervalMeasure E).toReal : ℂ)*((unitIntervalMeasure E').toReal : ℂ) := by
    field_simp
  rw [hmain, ← hz, ← mul_sub, norm_mul]
  calc
    _ ≤ ‖(H : ℂ)⁻¹^2‖*((F.card : ℝ)*(F.card : ℝ)*ε) :=
      mul_le_mul_of_nonneg_left hh (norm_nonneg _)
    _ = _ := by
      simp only [F, Finset.product_eq_sprod, card_product, card_range, Nat.cast_mul, norm_pow, norm_inv, Complex.norm_natCast]
      field_simp

end
end FiniteFactor

end OAI
