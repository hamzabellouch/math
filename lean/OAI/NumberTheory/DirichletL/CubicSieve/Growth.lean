import OAI.NumberTheory.DirichletL.CubicSieve.ExtractionOptimization

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
noncomputable section

def HasCubicExponent (ξ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
      sieveNorm M N ≤ C*(M*N)^ε*(M + N^ξ + (M*N)^(2/3 : ℝ))

theorem hasCubicExponent_initial : HasCubicExponent 2 := by
  intro ε hε
  let C := QuadraticInitialBound.initialSieveConstant
  have hC : 0 < C := QuadraticInitialBound.initialSieveConstant_pos
  refine ⟨4*C, by positivity, ?_⟩
  intro M N hM hN
  have hN0 : 0 ≤ N := by linarith
  have hceil : (⌈N⌉₊ : ℝ) ≤ 2*N := by
    have hh := Nat.ceil_lt_add_one hN0
    linarith
  have hn : (⌈N⌉₊ : ℝ)^2 ≤ 4*N^2 := by nlinarith [sq_nonneg ((⌈N⌉₊ : ℝ) - 2*N)]
  have hp : 1 ≤ (M*N)^ε := Real.one_le_rpow (by nlinarith [mul_nonneg (sub_nonneg.mpr hM) (sub_nonneg.mpr hN)]) hε.le
  have hx : 0 ≤ (M*N)^(2/3 : ℝ) := Real.rpow_nonneg (by positivity) _
  calc
    _ ≤ C*(M+(⌈N⌉₊ : ℝ)^2) := sieveNorm_initial M N hM hN
    _ ≤ 4*C*(M + N^(2 : ℝ) + (M*N)^(2/3 : ℝ)) := by
      rw [Real.rpow_two]
      nlinarith [mul_nonneg hC.le (sub_nonneg.mpr hn), mul_nonneg hC.le hx]
    _ ≤ _ := by
      have hs : 0 ≤ M + N^(2 : ℝ) + (M*N)^(2/3 : ℝ) := by positivity
      nlinarith [mul_nonneg (mul_nonneg (by positivity : 0 ≤ 4*C) hs) (sub_nonneg.mpr hp)]

lemma HasCubicExponent.swapped {ξ : ℝ} (h : HasCubicExponent ξ)
    (ε : ℝ) (hε : 0 < ε) : ∃ C : ℝ, 0 < C ∧
      ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
        sieveNorm M N ≤ C*(M*N)^ε*(M^ξ + N + (M*N)^(2/3 : ℝ)) := by
  obtain ⟨C,hC,hb⟩ := h ε hε
  refine ⟨C,hC,?_⟩
  intro M N hM hN
  rw [sieveNorm_reciprocity]
  simpa only [mul_comm, add_comm, add_left_comm, add_assoc] using hb N M hN hM

lemma HasCubicExponent.doubled {ξ : ℝ} (h : HasCubicExponent ξ)
    (ε : ℝ) (hε : 0 < ε) : ∃ C : ℝ, 0 < C ∧
      ∀ X N : ℝ, 1 ≤ X → 1 ≤ N →
        sieveNorm (2*X) N ≤ C*(X*N)^ε*(X^ξ + N + (X*N)^(2/3 : ℝ)) := by
  obtain ⟨C,hC,hb⟩ := h.swapped ε hε
  let A : ℝ := 1 + (2:ℝ)^ξ + (2:ℝ)^(2/3 : ℝ)
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨C*(2:ℝ)^ε*A, by positivity, ?_⟩
  intro X N hX hN
  have hX0 : 0 ≤ X := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hxξ := Real.rpow_nonneg hX0 ξ
  have hcross := Real.rpow_nonneg (mul_nonneg hX0 hN0) (2/3 : ℝ)
  have hshape : (2*X)^ξ + N + ((2*X)*N)^(2/3 : ℝ) ≤
      A*(X^ξ+N+(X*N)^(2/3 : ℝ)) := by
    rw [Real.mul_rpow (by norm_num) hX0]
    rw [show (2*X)*N = 2*(X*N) by ring, Real.mul_rpow (by norm_num) (mul_nonneg hX0 hN0)]
    dsimp only [A]
    nlinarith [mul_nonneg (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) ξ) hN0,
      mul_nonneg (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) ξ) hcross,
      mul_nonneg (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) (2/3 : ℝ)) hN0,
      mul_nonneg (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) (2/3 : ℝ)) hxξ]
  calc
    _ ≤ C*((2*X)*N)^ε*((2*X)^ξ+N+((2*X)*N)^(2/3 : ℝ)) := hb (2*X) N (by linarith) hN
    _ ≤ C*((2*X)*N)^ε*(A*(X^ξ+N+(X*N)^(2/3 : ℝ))) :=
      mul_le_mul_of_nonneg_left hshape (by positivity)
    _ = _ := by
      rw [show (2*X)*N = 2*(X*N) by ring, Real.mul_rpow (by norm_num) (mul_nonneg hX0 hN0)]
      ring

end
end SevenEighths.CubicSieve

end OAI
