import OAI.NumberTheory.DirichletL.CubicSieve.FrequencyDyads

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
noncomputable section

def frequencyMajorant (M N : ℝ) (j : ℕ) : ℝ :=
  elementSieveNorm ((2 : ℝ)^j) N / (1 + M * (2 : ℝ)^j / N^2)^3

lemma frequencyMajorant_nonneg (M N : ℝ) (hM : 0 ≤ M) (j : ℕ) :
    0 ≤ frequencyMajorant M N j := by
  unfold frequencyMajorant
  exact div_nonneg (elementSieveNorm_nonneg _ _) (by positivity)

lemma frequencyMajorant_geometric (M N : ℝ) (hM : 0 < M) (hN : 1 ≤ N) (j : ℕ) :
    frequencyMajorant M N j ≤
      (QuadraticInitialBound.initialSieveConstant * (1 + (⌈N⌉₊ : ℝ)^2) /
        (M / N^2)^3) * ((1 / 4 : ℝ)^j) := by
  let K : ℝ := (2 : ℝ)^j
  let c : ℝ := M / N^2
  let Q : ℝ := (⌈N⌉₊ : ℝ)^2
  let C : ℝ := QuadraticInitialBound.initialSieveConstant
  have hK : 1 ≤ K := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hK0 : 0 < K := by positivity
  have hN0 : 0 < N := by linarith
  have hc : 0 < c := by dsimp [c]; positivity
  have hQ : 0 ≤ Q := sq_nonneg _
  have hC : 0 ≤ C := QuadraticInitialBound.initialSieveConstant_pos.le
  have hi : elementSieveNorm K N ≤ C * (1 + Q) * K := by
    apply (elementSieveNorm_initial K N hK hN).trans
    dsimp only [C, Q]
    nlinarith [mul_nonneg hC (mul_nonneg hQ (sub_nonneg.mpr hK))]
  have hden : (c*K)^3 ≤ (1+c*K)^3 := by
    exact pow_le_pow_left₀ (by positivity) (by linarith) 3
  have hgeom : (K^2)⁻¹ = (1/4 : ℝ)^j := by
    dsimp only [K]
    rw [← pow_mul, Nat.mul_comm j 2, pow_mul, ← inv_pow]
    norm_num
  change elementSieveNorm K N / (1 + M*K/N^2)^3 ≤ _
  rw [show M*K/N^2 = c*K by dsimp [c]; ring]
  calc
    _ ≤ (C*(1+Q)*K) / (1+c*K)^3 := div_le_div_of_nonneg_right hi (by positivity)
    _ ≤ (C*(1+Q)*K) / (c*K)^3 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = (C*(1+Q)/c^3) * (K^2)⁻¹ := by field_simp
    _ = _ := by rw [hgeom]

theorem frequencyMajorant_summable (M N : ℝ) (hM : 0 < M) (hN : 1 ≤ N) :
    Summable (frequencyMajorant M N) := by
  have hg : Summable (fun j : ℕ => (1/4 : ℝ)^j) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  exact (hg.mul_left _).of_nonneg_of_le
    (frequencyMajorant_nonneg M N hM.le) (frequencyMajorant_geometric M N hM hN)

end
end SevenEighths.CubicSieve

end OAI
