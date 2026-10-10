import OAI.NumberTheory.Ostmann.QuadraticSieveComplementCorrelationsError
import OAI.NumberTheory.Ostmann.QuadraticSieveSquarefreeDyadic

namespace OAI

namespace Ostmann.QuadraticSieve
open scoped SchwartzMap

noncomputable def complementWindowLower (M T : ℝ) (v : ℕ) : ℝ :=
  Real.sqrt (M/squarefreeDyadicBase v)/(2*T)
noncomputable def complementWindowUpper (M T : ℝ) (v : ℕ) : ℝ :=
  2*T*Real.sqrt (M/squarefreeDyadicBase v)

theorem complementary_dyadic_window_parameters {M T : ℝ} (hM : 0 < M) (hT : 1 ≤ T)
    {v : ℕ} (hv : 0 < v) :
    0 < complementWindowLower M T v ∧
      complementWindowLower M T v ≤ Real.sqrt (M/v) ∧
      Real.sqrt (M/v) ≤ complementWindowUpper M T v ∧
      0 < T ∧ T ≤ min (Real.sqrt (M/v)/complementWindowLower M T v)
        (complementWindowUpper M T v/Real.sqrt (M/v)) ∧
      (complementWindowUpper M T v/Real.sqrt (M/v))^2 ≤ 16*T^2 := by
  obtain ⟨hB,hlo,hhi⟩ := squarefreeDyadicBase_bounds hv
  have hBr : (0 : ℝ) < squarefreeDyadicBase v := by exact_mod_cast hB
  obtain ⟨h1,h2⟩ := complementary_square_scale_window (v := (v : ℝ)) hM hBr
    (by exact_mod_cast hlo) (by exact_mod_cast hhi.le)
  exact poisson_window_parameters (Real.sqrt_pos.mpr (by positivity)) hT h1 h2

theorem complementaryCorrelation_window_error (W : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M T : ℝ) (K Δ N : ℕ) (S : Finset ℕ) (a : ℕ → ℂ),
      0 < M → 1 ≤ T → Δ ≠ 0 → (∀ n ∈ S, 0 < n ∧ n ≤ N) →
      ‖complementaryCorrelation W M K Δ S a -
        complementaryCorrelationMain W M K Δ S a (complementWindowLower M T)
          (complementWindowUpper M T) (fun _ => 16*T^2)‖ ≤
        C*(N : ℝ)*K*Real.sqrt M/T^A*coefficientEnergy S a := by
  obtain ⟨C,hC,hbound⟩ := complementaryCorrelation_error W A
  refine ⟨C,hC,?_⟩
  intro M T K Δ N S a hM hT hΔ hS
  have hTp : 0 < T := by linarith
  have h := hbound M hM K Δ N hΔ S a hS
    (complementWindowLower M T) (complementWindowUpper M T) (fun _ => T) (fun _ => 16*T^2)
    (fun v hv => complementary_dyadic_window_parameters hM hT (mem_oddSquarefreeUpTo.mp hv).1)
  have hcard : (oddSquarefreeUpTo K).card ≤ K := by
    calc
      _ ≤ (Finset.Icc 1 K).card := Finset.card_le_card (fun v hv =>
        Finset.mem_Icc.mpr ⟨(mem_oddSquarefreeUpTo.mp hv).1,(mem_oddSquarefreeUpTo.mp hv).2.1⟩)
      _ = _ := by simp
  have hsum : (∑ v ∈ oddSquarefreeUpTo K, Real.sqrt (M/v)/T^A) ≤
      (K : ℝ)*Real.sqrt M/T^A := by
    calc
      _ ≤ ∑ _v ∈ oddSquarefreeUpTo K, Real.sqrt M/T^A := by
        apply Finset.sum_le_sum
        intro v hv
        apply div_le_div_of_nonneg_right _ (by positivity)
        apply Real.sqrt_le_sqrt
        exact div_le_self hM.le (by exact_mod_cast (mem_oddSquarefreeUpTo.mp hv).1)
      _ = (oddSquarefreeUpTo K).card*(Real.sqrt M/T^A) := by rw [Finset.sum_const,nsmul_eq_mul]
      _ ≤ (K : ℝ)*(Real.sqrt M/T^A) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
      _ = _ := by ring
  apply h.trans
  have hE := coefficientEnergy_nonneg S a
  calc
    _ ≤ C*(N : ℝ)*coefficientEnergy S a*((K : ℝ)*Real.sqrt M/T^A) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

end Ostmann.QuadraticSieve

end OAI
