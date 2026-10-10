import OAI.NumberTheory.Ostmann.QuadraticSieveExponentIterationThreshold
import OAI.NumberTheory.Ostmann.QuadraticSieveRowInflationScale

namespace OAI

noncomputable section
namespace Ostmann.QuadraticSieve

theorem exists_dyadicInflation_scale (C δ : ℝ) (hC : 0 < C) (hδ : 0 < δ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (M N : ℕ) (X : ℝ), 0 < M → 0 < N → 1 ≤ X →
      ∃ L : ℕ, M ≤ L ∧ X ≤ L ∧ C*(M:ℝ)*Real.log (2*(M:ℝ)*N) ≤ L ∧
        (L:ℝ) ≤ B*((M:ℝ)*N)^δ*((M:ℝ)+X) := by
  let A : ℝ := 1+C*(Real.log 2+1/δ)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hA1 : 1 ≤ A := by
    dsimp [A]
    have hh : 0 ≤ C*(Real.log 2+1/δ) := by positivity
    linarith
  have hAp : 0 < A := by linarith
  refine ⟨A+1,by positivity,?_⟩
  intro M N X hM hN hX
  let P : ℝ := (M:ℝ)*N
  have hM1 : (1:ℝ) ≤ M := by exact_mod_cast hM
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hP1 : 1 ≤ P := one_le_mul_of_one_le_of_one_le hM1 hN1
  have hPp : 0 < P := by linarith
  have hp1 : 1 ≤ P^δ := Real.one_le_rpow hP1 hδ.le
  have hp0 : 0 ≤ P^δ := by positivity
  have hlog : Real.log (2*(M:ℝ)*N) ≤ (Real.log 2+1/δ)*P^δ := by
    have hh := Real.log_le_rpow_div hPp.le hδ
    have h2 := mul_le_mul_of_nonneg_left hp1 hl2.le
    rw [show 2*(M:ℝ)*N=2*P by dsimp [P]; ring,
      Real.log_mul (by norm_num) hPp.ne']
    simp only [div_eq_mul_inv] at hh ⊢
    nlinarith
  let Y : ℝ := A*P^δ*((M:ℝ)+X)
  have hsum : 1 ≤ (M:ℝ)+X := by linarith
  have hbase : (M:ℝ)+X ≤ P^δ*((M:ℝ)+X) :=
    le_mul_of_one_le_left (by linarith) hp1
  have hbase' : P^δ*((M:ℝ)+X) ≤ Y := by
    dsimp [Y]
    have hh := mul_le_mul_of_nonneg_right hA1
      (show 0 ≤ P^δ*((M:ℝ)+X) by positivity)
    nlinarith
  have hMY : (M:ℝ) ≤ Y := by linarith
  have hXY : X ≤ Y := by linarith
  have hY0 : 0 ≤ Y := by linarith
  have hcost : C*(M:ℝ)*Real.log (2*(M:ℝ)*N) ≤ Y := by
    have h1 := mul_le_mul_of_nonneg_left hlog (show 0 ≤ C*(M:ℝ) by positivity)
    have hcoeff : C*(Real.log 2+1/δ) ≤ A := by dsimp [A]; linarith
    have h2 := mul_le_mul_of_nonneg_right hcoeff
      (show 0 ≤ P^δ*(M:ℝ) by positivity)
    have h3 : A*P^δ*(M:ℝ) ≤ Y := by
      dsimp [Y]
      exact mul_le_mul_of_nonneg_left (by linarith : (M:ℝ)≤(M:ℝ)+X) (by positivity)
    nlinarith
  refine ⟨⌈Y⌉₊,?_,hXY.trans (Nat.le_ceil Y),hcost.trans (Nat.le_ceil Y),?_⟩
  · exact_mod_cast hMY.trans (Nat.le_ceil Y)
  · have hh := (Nat.ceil_lt_add_one hY0).le
    have hb : 1 ≤ P^δ*((M:ℝ)+X) := hsum.trans hbase
    dsimp [Y] at hh
    dsimp [P] at *
    nlinarith

theorem exists_inflated_dyadic_threshold (δ : ℝ) (hδ : 0 < δ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (M N : ℕ) (X : ℝ), 0 < M → 0 < N → 1 ≤ X →
      ∀ S : Finset ℕ, S ⊆ oddSquarefreeUpTo N → ∃ M' : ℕ,
      0 < M' ∧ (M:ℝ) ≤ M' ∧ X ≤ M' ∧
      (M':ℝ) ≤ B*((M:ℝ)*N)^δ*((M:ℝ)+X) ∧
      quadraticNorm (dyadicSquarefreeRows M) S ≤ 20*quadraticNorm (dyadicSquarefreeRows M') S := by
  obtain ⟨C,hC,hbound⟩ := exists_quadraticNorm_rowInflation_at_scale
  obtain ⟨B,hB,hscale⟩ := exists_dyadicInflation_scale C δ (by linarith) hδ
  refine ⟨32*B,by positivity,?_⟩
  intro M N X hM hN hX S hS
  obtain ⟨L,hML,hXL,hcost,hL⟩ := hscale M N X hM hN hX
  obtain ⟨M',hLM',hM'L,hQ⟩ := hbound M N L hM hN hML hcost S hS
  have hMM' : M ≤ M' := hML.trans hLM'
  have hLMr : (L:ℝ) ≤ M' := by exact_mod_cast hLM'
  have hM'Lr : (M':ℝ) ≤ 32*L := by exact_mod_cast hM'L
  refine ⟨M',lt_of_lt_of_le hM hMM',by exact_mod_cast hMM',hXL.trans hLMr,?_,hQ⟩
  nlinarith

end Ostmann.QuadraticSieve

end

end OAI
