import OAI.NumberTheory.CubicMoment.Estimates.NoncubeSieveAssembly

namespace OAI

/-! A fixed dilation of the coefficient support changes the three sieve
constants, while preserving their common conductor exponents. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma cubic_sieve_fixed_dilation {K N U ε : ℝ} (hK : 1 ≤ K)
    (hN : 0 ≤ N) (hU : 0 ≤ U) (_hε : 0 ≤ ε) :
    (U*(K*N))^ε*(U+K*N+(U*(K*N))^(2/3:ℝ)) ≤
      K^(1+ε)*((U*N)^ε*(U+N+(U*N)^(2/3:ℝ))) := by
  have hKp : 0 < K := zero_lt_one.trans_le hK
  have hKt : K^(2/3:ℝ) ≤ K := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hK (by norm_num : (2/3:ℝ) ≤ 1)
  have hid : U*(K*N) = K*(U*N) := by ring
  rw [hid,Real.mul_rpow hKp.le (mul_nonneg hU hN),Real.mul_rpow hKp.le (mul_nonneg hU hN)]
  have hs : U+K*N+K^(2/3:ℝ)*(U*N)^(2/3:ℝ) ≤ K*(U+N+(U*N)^(2/3:ℝ)) := by
    nlinarith [mul_le_mul_of_nonneg_right hK hU,
      mul_le_mul_of_nonneg_right hKt (Real.rpow_nonneg (mul_nonneg hU hN) (2/3:ℝ))]
  calc
    _ ≤ (K^ε*(U*N)^ε)*(K*(U+N+(U*N)^(2/3:ℝ))) :=
      mul_le_mul_of_nonneg_left hs (mul_nonneg (Real.rpow_nonneg hKp.le _) (Real.rpow_nonneg (mul_nonneg hU hN) _))
    _ = _ := by rw [Real.rpow_add hKp,Real.rpow_one]; ring

lemma ordinary_sieve_fixed_dilation {K N U V ε : ℝ} (hK : 1 ≤ K)
    (hN : 0 ≤ N) (hU : 0 ≤ U) (hV : 0 ≤ V) (hε : 0 ≤ ε) :
    (U*V)^ε*((U*V)^2+K*N) ≤ K^(1+ε)*((U*V)^ε*((U*V)^2+N)) := by
  have hKp : 0 < K := zero_lt_one.trans_le hK
  have hKK : K ≤ K^(1+ε) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hK (show (1:ℝ) ≤ 1+ε by linarith)
  have hs : (U*V)^2+K*N ≤ K*((U*V)^2+N) := by
    nlinarith [mul_le_mul_of_nonneg_right hK (sq_nonneg (U*V))]
  calc
    _ ≤ (U*V)^ε*(K*((U*V)^2+N)) :=
      mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg (mul_nonneg hU hV) _)
    _ = K*((U*V)^ε*((U*V)^2+N)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hKK (mul_nonneg
      (Real.rpow_nonneg (mul_nonneg hU hV) _) (by positivity))

theorem dilated_noncube_three_sieve_bounds (hHuxley : HuxleyAdditiveLargeSieve)
    {K ε : ℝ} (hK : 1 ≤ K) (hε : 0 < ε) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
    ∀ (B R S T J H : Finset Eisenstein) (N U V : ℝ),
      1 ≤ N → 1 ≤ U → 1 ≤ V →
      (∀ b ∈ B, primary b ∧ Squarefree b ∧ norm b ≤ K*N) →
      (∀ s ∈ S, primary s ∧ Squarefree s ∧ norm s ≤ U) →
      (∀ t ∈ T, primary t ∧ Squarefree t ∧ norm t ≤ V) →
      H ⊆ coprimeResidualSupport R J (coprimePairs S T) →
      ∀ β : Eisenstein → ℂ,
      (∑ h ∈ H, ‖∑ b ∈ B, β b*cubicSymbol b h‖^2) ≤
        min ((R.card:ℝ)*J.card*C₁ *
          min ((T.card:ℝ)*(U*N)^ε*(U+N+(U*N)^(2/3:ℝ)))
              ((S.card:ℝ)*(V*N)^ε*(V+N+(V*N)^(2/3:ℝ))))
          ((R.card:ℝ)*J.card*C₂*(U*V)^ε*((U*V)^2+N)) *
            ∑ b ∈ B, ‖β b‖^2 := by
  obtain ⟨C₁,C₂,hC₁,hC₂,hraw⟩ := noncube_three_sieve_bounds hHuxley hε
  let D := K^(1+ε)
  have hD : 0 < D := Real.rpow_pos_of_pos (zero_lt_one.trans_le hK) _
  refine ⟨C₁*D,C₂*D,mul_pos hC₁ hD,mul_pos hC₂ hD,?_⟩
  intro B R S T J H N U V hN hU hV hB hS hT hH β
  have hN0 : 0 ≤ N := by linarith
  have hU0 : 0 ≤ U := by linarith
  have hV0 : 0 ≤ V := by linarith
  have hm := hraw B R S T J H (K*N) U V (one_le_mul_of_one_le_of_one_le hK hN)
    hU hV hB hS hT hH β
  apply hm.trans
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  apply min_le_min
  · have h₁ : (T.card:ℝ)*(U*(K*N))^ε*(U+K*N+(U*(K*N))^(2/3:ℝ)) ≤
        D*((T.card:ℝ)*(U*N)^ε*(U+N+(U*N)^(2/3:ℝ))) := by
      convert mul_le_mul_of_nonneg_left (cubic_sieve_fixed_dilation hK hN0 hU0 hε.le)
        (Nat.cast_nonneg T.card) using 1 <;> (try dsimp only [D]) <;> ring
    have h₂ : (S.card:ℝ)*(V*(K*N))^ε*(V+K*N+(V*(K*N))^(2/3:ℝ)) ≤
        D*((S.card:ℝ)*(V*N)^ε*(V+N+(V*N)^(2/3:ℝ))) := by
      convert mul_le_mul_of_nonneg_left (cubic_sieve_fixed_dilation hK hN0 hV0 hε.le)
        (Nat.cast_nonneg S.card) using 1 <;> (try dsimp only [D]) <;> ring
    have hh := min_le_min h₁ h₂
    rw [← mul_min_of_nonneg _ _ hD.le] at hh
    have hf := mul_le_mul_of_nonneg_left hh
      (show 0 ≤ (R.card:ℝ)*J.card*C₁ by positivity)
    convert hf using 1; ring
  · have hf := mul_le_mul_of_nonneg_left (ordinary_sieve_fixed_dilation hK hN0 hU0 hV0 hε.le)
      (show 0 ≤ (R.card:ℝ)*J.card*C₂ by positivity)
    convert hf using 1 <;> (try dsimp only [D]) <;> ring

end CubicFirstMoment

end

end OAI
