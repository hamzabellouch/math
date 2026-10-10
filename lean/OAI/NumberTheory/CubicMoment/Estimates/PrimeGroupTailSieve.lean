import OAI.NumberTheory.CubicMoment.Estimates.PrimeGroupTailNumerical

namespace OAI

/-! An actual finite frequency-block estimate for arbitrary squarefree
coefficients. There is no prime-convolution or height restriction. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem primeGroupTail_frequency_sieve (hHuxley : HuxleyAdditiveLargeSieve)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (B R S T J H : Finset Eisenstein) (N U V : ℝ),
      1 ≤ N → 1 ≤ U → 1 ≤ V → U*V^2 ≤ N^(19/20:ℝ) →
      (∀ b ∈ B, primary b ∧ Squarefree b ∧ norm b ≤ N) →
      (∀ s ∈ S, primary s ∧ Squarefree s ∧ norm s ≤ U) →
      (∀ t ∈ T, primary t ∧ Squarefree t ∧ norm t ≤ V) →
      (T.card:ℝ) ≤ 18*V →
      H ⊆ coprimeResidualSupport R J (coprimePairs S T) →
      ∀ β : Eisenstein → ℂ,
      (∑ h ∈ H, ‖∑ b ∈ B, β b*cubicSymbol b h‖^2) ≤
        (R.card:ℝ)*J.card*C*N^(2*ε)*
          (N+3*N^(119/120:ℝ)*(U*V^2)^(1/3:ℝ))*∑ b ∈ B, ‖β b‖^2 := by
  obtain ⟨C₁,C₂,hC₁,hC₂,hbound⟩ := noncube_three_sieve_bounds hHuxley hε
  refine ⟨18*C₁+C₂,by positivity,?_⟩
  intro B R S T J H N U V hN hU hV hD hB hS hT hcard hH β
  let C := 18*C₁+C₂
  let F : ℝ := R.card*J.card
  let E := ∑ b ∈ B, ‖β b‖^2
  let K := F*C*N^(2*ε)*E
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hE : 0 ≤ E := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hN0 : 0 ≤ N := zero_le_one.trans hN
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hU0 : 0 ≤ U := zero_le_one.trans hU
  have hV0 : 0 ≤ V := zero_le_one.trans hV
  have hDN : U*V^2 ≤ N := hD.trans (by
    nth_rw 2 [← Real.rpow_one N]
    exact Real.rpow_le_rpow_of_exponent_le hN (by norm_num))
  have hUN : U ≤ N := (le_mul_of_one_le_right hU0 (one_le_pow₀ hV)).trans hDN
  have hVN : V ≤ N := (show V ≤ V^2 by nlinarith).trans
    ((le_mul_of_one_le_left (sq_nonneg V) hU).trans hDN)
  have hpow (x : ℝ) (hx : 0 ≤ x) (hxN : x ≤ N^2) : x^ε ≤ N^(2*ε) := by
    apply (Real.rpow_le_rpow hx hxN hε.le).trans_eq
    rw [← Real.rpow_natCast N 2,← Real.rpow_mul hN0]
    norm_num
  have hpowU : (U*N)^ε ≤ N^(2*ε) := hpow _ (mul_nonneg hU0 hN0) (by nlinarith)
  have hpowUV : (U*V)^ε ≤ N^(2*ε) := hpow _ (mul_nonneg hU0 hV0) (by nlinarith)
  have hcoeff : C₁*(T.card:ℝ)*(U*N)^ε ≤ C*V*N^(2*ε) := by
    calc
      _ ≤ C₁*(18*V)*N^(2*ε) := by gcongr
      _ = (18*C₁)*V*N^(2*ε) := by ring
      _ ≤ _ := by gcongr; dsimp [C]; linarith
  have hcoeff' : C₂*(U*V)^ε ≤ C*N^(2*ε) := by
    gcongr
    · dsimp [C]; linarith
  have hraw := hbound B R S T J H N U V hN hU hV hB hS hT hH β
  have hcubic : (∑ h ∈ H, ‖∑ b ∈ B, β b*cubicSymbol b h‖^2) ≤
      K*(V*(U+N+(U*N)^(2/3:ℝ))) := by
    calc
      _ ≤ _ := hraw
      _ ≤ (F*C₁*((T.card:ℝ)*(U*N)^ε*(U+N+(U*N)^(2/3:ℝ))))*E := by
        apply mul_le_mul_of_nonneg_right _ hE
        exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity))
      _ = F*(C₁*(T.card:ℝ)*(U*N)^ε)*(U+N+(U*N)^(2/3:ℝ))*E := by ring
      _ ≤ F*(C*V*N^(2*ε))*(U+N+(U*N)^(2/3:ℝ))*E := by gcongr
      _ = _ := by dsimp [K]; ring
  have hord : (∑ h ∈ H, ‖∑ b ∈ B, β b*cubicSymbol b h‖^2) ≤
      K*((U*V)^2+N) := by
    calc
      _ ≤ _ := hraw
      _ ≤ ((R.card:ℝ)*J.card*C₂*(U*V)^ε*((U*V)^2+N))*E :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) hE
      _ = F*(C₂*(U*V)^ε)*((U*V)^2+N)*E := by dsimp [F]; ring
      _ ≤ F*(C*N^(2*ε))*((U*V)^2+N)*E := by gcongr
      _ = _ := by dsimp [K]; ring
  have hK : 0 ≤ K := by dsimp [K]; positivity
  calc
    _ ≤ min (K*(V*(U+N+(U*N)^(2/3:ℝ)))) (K*((U*V)^2+N)) := le_min hcubic hord
    _ = K*min (V*(U+N+(U*N)^(2/3:ℝ))) ((U*V)^2+N) := (mul_min_of_nonneg _ _ hK).symm
    _ ≤ K*(N+3*N^(119/120:ℝ)*(U*V^2)^(1/3:ℝ)) :=
      mul_le_mul_of_nonneg_left (primeGroupTail_sieve_min hU hV hN hD) hK
    _ = _ := by dsimp [K,F,C,E]; ring

end CubicFirstMoment

end

end OAI
