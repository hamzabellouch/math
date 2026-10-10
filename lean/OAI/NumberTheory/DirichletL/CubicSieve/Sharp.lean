import OAI.NumberTheory.DirichletL.CubicSieve.ExponentImprovement

namespace OAI

namespace SevenEighths.CubicSieve
noncomputable section

theorem hasCubicExponent_four_thirds : HasCubicExponent (4/3 : ℝ) := by
  intro ε hε
  obtain ⟨ξ, hξ, hξ2, hξε, hx⟩ := SevenEighths.HeathBrownIteration.finite_improvement
    hasCubicExponent_initial (fun x hx hx2 hp => hp.improve hx hx2)
    (show 0 < ε/2 by positivity)
  obtain ⟨C,hC,hb⟩ := hx (ε/2) (by positivity)
  refine ⟨C,hC,?_⟩
  intro M N hM hN
  have hM0 : 0 < M := by linarith
  have hN0 : 0 < N := by linarith
  have hMN : 0 < M*N := mul_pos hM0 hN0
  have hp : 1 ≤ N^(ε/2) := Real.one_le_rpow hN (by positivity)
  have hNpow : N^ξ ≤ N^(4/3 : ℝ)*N^(ε/2) := by
    rw [← Real.rpow_add hN0]
    exact Real.rpow_le_rpow_of_exponent_le hN hξε.le
  have hcross : 0 ≤ (M*N)^(2/3 : ℝ) := Real.rpow_nonneg hMN.le _
  have hs : M+N^ξ+(M*N)^(2/3 : ℝ) ≤
      N^(ε/2)*(M+N^(4/3 : ℝ)+(M*N)^(2/3 : ℝ)) := by
    nlinarith [mul_nonneg hM0.le (sub_nonneg.mpr hp),
      mul_nonneg hcross (sub_nonneg.mpr hp)]
  have hnp : N^(ε/2) ≤ (M*N)^(ε/2) :=
    Real.rpow_le_rpow hN0.le (by nlinarith) (by positivity)
  calc
    _ ≤ C*(M*N)^(ε/2)*(M+N^ξ+(M*N)^(2/3 : ℝ)) := hb M N hM hN
    _ ≤ C*(M*N)^(ε/2)*(N^(ε/2)*(M+N^(4/3 : ℝ)+(M*N)^(2/3 : ℝ))) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ ≤ C*(M*N)^(ε/2)*((M*N)^(ε/2)*(M+N^(4/3 : ℝ)+(M*N)^(2/3 : ℝ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hnp (by positivity)) (by positivity)
    _ = _ := by
      have he : (M*N)^(ε/2)*(M*N)^(ε/2) = (M*N)^ε := by
        rw [← Real.rpow_add hMN]
        congr 1
        ring
      calc
        _ = C*((M*N)^(ε/2)*(M*N)^(ε/2))*(M+N^(4/3 : ℝ)+(M*N)^(2/3 : ℝ)) := by ring
        _ = _ := by rw [he]

lemma four_thirds_le_cross (M N : ℝ) (_hM : 1 ≤ M) (hN : 1 ≤ N) (hNM : N ≤ M) :
    N^(4/3 : ℝ) ≤ (M*N)^(2/3 : ℝ) := by
  have hN0 : 0 ≤ N := by linarith
  calc
    N^(4/3 : ℝ) = (N*N)^(2/3 : ℝ) := by
      rw [Real.mul_rpow hN0 hN0, ← Real.rpow_add (by linarith : 0 < N)]
      norm_num
    _ ≤ _ := Real.rpow_le_rpow (mul_nonneg hN0 hN0)
      (mul_le_mul_of_nonneg_right hNM hN0) (by norm_num)

theorem sieveNorm_sharp (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
      sieveNorm M N ≤ C*(M*N)^ε*(M+N+(M*N)^(2/3 : ℝ)) := by
  obtain ⟨C,hC,hb⟩ := hasCubicExponent_four_thirds ε hε
  refine ⟨2*C,by positivity,?_⟩
  intro M N hM hN
  have hM0 : 0 ≤ M := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hcross : 0 ≤ (M*N)^(2/3 : ℝ) := Real.rpow_nonneg (mul_nonneg hM0 hN0) _
  by_cases hNM : N ≤ M
  · have hh := four_thirds_le_cross M N hM hN hNM
    calc
      _ ≤ C*(M*N)^ε*(M+N^(4/3 : ℝ)+(M*N)^(2/3 : ℝ)) := hb M N hM hN
      _ ≤ C*(M*N)^ε*(2*(M+N+(M*N)^(2/3 : ℝ))) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = _ := by ring
  · have hMN := le_of_not_ge hNM
    have hh := four_thirds_le_cross N M hN hM hMN
    have hs : N+M^(4/3 : ℝ)+(N*M)^(2/3 : ℝ) ≤
        2*(M+N+(M*N)^(2/3 : ℝ)) := by
      rw [mul_comm N M] at hh ⊢
      linarith
    calc
      _ = sieveNorm N M := sieveNorm_reciprocity M N
      _ ≤ C*(N*M)^ε*(N+M^(4/3 : ℝ)+(N*M)^(2/3 : ℝ)) := hb N M hN hM
      _ ≤ C*(N*M)^ε*(2*(M+N+(M*N)^(2/3 : ℝ))) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := by rw [mul_comm N M]; ring

end
end SevenEighths.CubicSieve

end OAI
