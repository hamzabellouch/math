import OAI.NumberTheory.CubicMoment.Estimates.OuterSieveDilation
import OAI.NumberTheory.CubicMoment.Estimates.NoncubeSieveAssembly

namespace OAI

/-! The outer cubic sieve on one actual frequency core block. This is
valid for arbitrary squarefree coefficients, hence for the shortened
common-divisor rows. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem outer_core_block_sieve {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S H : Finset Eisenstein) (B N : ℝ) (i j : ℕ),
      0 ≤ B → 1 ≤ N → coreDyadicConductor i j ≤ B →
      (∀ n ∈ S, primary n ∧ Squarefree n ∧ norm n ≤ N) →
      H ⊆ coreDyadicBlock B i j → ∀ β : Eisenstein → ℂ,
      (∑ h ∈ H, ‖∑ n ∈ S, β n*cubicSymbol n h‖^2) ≤
        C*(2*B*N)^ε*(B+(B*N)^(2/3:ℝ)+B^(1/3:ℝ)*N)*
          ∑ n ∈ S, ‖β n‖^2 := by
  obtain ⟨C₀,hC₀,hbound⟩ := residualFrequency_sieve_bound ε hε
  let R := nonzeroNormBall 729
  let C := (R.card:ℝ)*18*C₀*72
  refine ⟨C+1,by dsimp [C]; positivity,?_⟩
  intro S H B N i j hB hN hDB hS hH β
  let P : ℝ := 2^i
  let Q : ℝ := 2^j
  have hP : 1 ≤ P := one_le_pow₀ (by norm_num)
  have hQ : 1 ≤ Q := one_le_pow₀ (by norm_num)
  have hP0 := zero_le_one.trans hP
  have hQ0 := zero_le_one.trans hQ
  have hPQ : P*Q^2 ≤ B := hDB
  have hPB : P ≤ B := (le_mul_of_one_le_right hP0 (one_le_pow₀ hQ)).trans hPQ
  have hQB : Q ≤ B := (by nlinarith [sq_nonneg (Q-1),mul_le_mul_of_nonneg_right hP (sq_nonneg Q)] : Q ≤ P*Q^2).trans hPQ
  have hp (n : Eisenstein) (hn : n ∈ squarefreePrimaryDyad i) :
      primary n ∧ Squarefree n ∧ norm n ≤ 2*P := by
    have hh := squarefreePrimaryDyad_gramDyad hn
    exact ⟨hh.1,hh.2.1,hh.2.2.2.le⟩
  have hq (n : Eisenstein) (hn : n ∈ squarefreePrimaryDyad j) :
      primary n ∧ Squarefree n ∧ norm n ≤ 2*Q := by
    have hh := squarefreePrimaryDyad_gramDyad hn
    exact ⟨hh.1,hh.2.1,hh.2.2.2.le⟩
  have hpCard : ((squarefreePrimaryDyad i).card:ℝ) ≤ 36*P := by
    have hh := primary_support_card_le (squarefreePrimaryDyad i) (by positivity : 0 ≤ 2*P)
      (fun n hn => ⟨(hp n hn).1,(hp n hn).2.2⟩)
    linarith
  have hqCard : ((squarefreePrimaryDyad j).card:ℝ) ≤ 36*Q := by
    have hh := primary_support_card_le (squarefreePrimaryDyad j) (by positivity : 0 ≤ 2*Q)
      (fun n hn => ⟨(hq n hn).1,(hq n hn).2.2⟩)
    linarith
  have hcCard : ((coreDyadicCubeFactors B i j).card:ℝ) ≤
      18*(B/(P*Q^2))^(1/3:ℝ) :=
    nonzeroNormBall_card_le (Real.rpow_nonneg (div_nonneg hB (coreDyadicConductor_pos i j).le) _)
  have hh := (frequency_subset_mass_le H _ S
    (hH.trans (coprimeResidualSupport_subset R (coreDyadicCubeFactors B i j)
      (squarefreePrimaryDyad i) (squarefreePrimaryDyad j))) β).trans
    (hbound S R (squarefreePrimaryDyad i) (squarefreePrimaryDyad j)
      (coreDyadicCubeFactors B i j) N (2*P) (2*Q) hN (by linarith) (by linarith) hS hp hq β)
  have hmin := outer_dyadic_sieve_min hP0 hPB hQ0 hQB (zero_le_one.trans hN)
    (Nat.cast_nonneg (squarefreePrimaryDyad i).card) hpCard
    (Nat.cast_nonneg (squarefreePrimaryDyad j).card) hqCard hε.le
  have houter := outer_sieve_power_min hP hQ hPQ (zero_le_one.trans hN)
  have hE : 0 ≤ ∑ n ∈ S, ‖β n‖^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  calc
    _ ≤ (R.card:ℝ)*(18*(B/(P*Q^2))^(1/3:ℝ))*C₀*
        ((72*(2*B*N)^ε)*
          min (Q*(P+N+(P*N)^(2/3:ℝ))) (P*(Q+N+(Q*N)^(2/3:ℝ))))*
        ∑ n ∈ S, ‖β n‖^2 := by
      apply hh.trans
      gcongr
    _ = C*(2*B*N)^ε*((B/(P*Q^2))^(1/3:ℝ)*
        min (Q*(P+N+(P*N)^(2/3:ℝ))) (P*(Q+N+(Q*N)^(2/3:ℝ))))*
        ∑ n ∈ S, ‖β n‖^2 := by dsimp only [C]; ring
    _ ≤ C*(2*B*N)^ε*(B+(B*N)^(2/3:ℝ)+B^(1/3:ℝ)*N)*
        ∑ n ∈ S, ‖β n‖^2 := by gcongr
    _ ≤ _ := by gcongr; linarith

end CubicFirstMoment

end

end OAI
