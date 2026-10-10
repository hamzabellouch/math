import OAI.MeasureTheory.Falconer.Recursion.ProfileIterationBudget
import OAI.MeasureTheory.Falconer.Incidence.ProfileBlockBudget

namespace OAI

/-! Choose the block width after fixing the maximal number of intervals.
All recursive losses then fit a prescribed weak exponent uniformly in depth. -/
namespace Falconer

theorem exists_uniform_profile_iteration_budget {ε : ℝ} (hε : 0 < ε) (J : ℕ) :
    ∃ B : ℕ, 0 < B ∧ Even B ∧ ∃ lam : ℝ, 0 < lam ∧ ∃ N0 : ℕ, 0 < N0 ∧
      ∀ m : ℕ, 0 < m → N0 ≤ B*m → ∀ j : ℕ, j ≤ J →
        let N := B*m
        let H : ℝ := (4*(N+2)+11:ℕ)
        let G := (2:ℝ)^(3*(m+1))*((2*B+1:ℕ):ℝ)^(m+1)
        profileBudgetSequence H G ((2:ℝ)^(lam*(N:ℝ))) j ≤ (2:ℝ)^(ε*(N:ℝ)) ∧
        G ≤ (2:ℝ)^((lam/4)*(N:ℝ)) := by
  let p : ℝ := ((2^J:ℕ):ℝ)
  have hp : 0 < p := by dsimp [p]; positivity
  let lam := ε/(4*p)
  have hlam : 0 < lam := by dsimp [lam]; positivity
  obtain ⟨B,hB,hBeven,hblock⟩ := exists_even_profile_block_budget (show 0 < lam/4 by positivity) 3
  obtain ⟨N0,hN0,hpoly⟩ := dyadic_polynomial_loss hlam
    (show 0 ≤ (1024:ℝ)*19^3 by positivity) 3
  refine ⟨B,hB,hBeven,lam,hlam,N0,hN0,?_⟩
  intro m hm hN j hj
  let N := B*m
  let H : ℝ := (4*(N+2)+11:ℕ)
  let G := (2:ℝ)^(3*(m+1))*((2*B+1:ℕ):ℝ)^(m+1)
  have hN0' : N0 ≤ N := hN
  have hH0 : 0 ≤ H := by dsimp [H]; positivity
  have hH : 1 ≤ H := by dsimp [H]; exact_mod_cast (show 1 ≤ 4*(N+2)+11 by omega)
  have hG : 1 ≤ G := profile_label_cost_one_le B (m+1)
  have hGsmall : G ≤ (2:ℝ)^((lam/4)*(N:ℝ)) := by
    simpa only [G,N,mul_comm] using hblock m hm
  have hGbound : G ≤ (2:ℝ)^(lam*(N:ℝ)) := hGsmall.trans
    (Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_right (by linarith only [hlam] : lam/4 ≤ lam) (Nat.cast_nonneg N)))
  have hHbound : H ≤ 19*((N:ℝ)+1) := by
    dsimp [H]
    push_cast
    nlinarith only [Nat.cast_nonneg (α := ℝ) N]
  have hpolybound : 1024*H^3 ≤ (2:ℝ)^(lam*(N:ℝ)) := by
    calc
      _ ≤ (1024:ℝ)*(19*((N:ℝ)+1))^3 := by gcongr
      _ = (1024:ℝ)*19^3*((N:ℝ)+1)^3 := by ring
      _ ≤ Real.exp (lam*(N:ℝ)*Real.log 2) := hpoly N hN0'
      _ = _ := by rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]; congr 1; ring
  have hC : 1024*H^3*G ≤ (2:ℝ)^((2*lam)*(N:ℝ)) := by
    calc
      _ ≤ (2:ℝ)^(lam*(N:ℝ))*(2:ℝ)^(lam*(N:ℝ)) :=
        mul_le_mul hpolybound hGbound (zero_le_one.trans hG) (by positivity)
      _ = _ := by rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]; congr 1; ring
  have hW : 1 ≤ (2:ℝ)^(lam*(N:ℝ)) := Real.one_le_rpow (by norm_num) (by positivity)
  have hlast := profileBudgetSequence_power_bound hH0 (zero_le_one.trans hG)
    (show 0 ≤ (2:ℝ)^(lam*(N:ℝ)) by positivity) hC le_rfl J
  have hpow : (((2^J-1:ℕ):ℝ)*(2*lam)+((2^J:ℕ):ℝ)*lam) ≤ ε := by
    have hsub : ((2^J-1:ℕ):ℝ) ≤ p := by dsimp [p]; exact_mod_cast Nat.sub_le (2^J) 1
    have he : p*lam = ε/4 := by dsimp [lam]; field_simp
    have hh := mul_le_mul_of_nonneg_right hsub (show 0 ≤ 2*lam by positivity)
    nlinarith only [hh,he,hε]
  refine ⟨?_,hGsmall⟩
  calc
    _ ≤ profileBudgetSequence H G ((2:ℝ)^(lam*(N:ℝ))) J :=
      profileBudgetSequence_monotone hH hG hW hj
    _ ≤ (2:ℝ)^((((2^J-1:ℕ):ℝ)*(2*lam)+((2^J:ℕ):ℝ)*lam)*(N:ℝ)) := hlast
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg N))

end Falconer

end OAI
