import OAI.NumberTheory.CubicMoment.Estimates.SmallBCoreBlock

namespace OAI

/-! Retain the conductor, rather than length, loss of the ordinary sieve.
This gives logarithmic savings for moderately small noncube cores. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem smallB_core_ordinary_sieve (hHuxley : HuxleyAdditiveLargeSieve) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S H : Finset Eisenstein) (β : Eisenstein → ℂ)
      (N B : ℝ) (i j : ℕ), 1 ≤ N → 0 ≤ B →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ norm b ≤ N) →
      (8*coreDyadicConductor i j)^2 ≤ N → H ⊆ coreDyadicBlock B i j →
      (∑ h ∈ H, ‖∑ b ∈ S, β b*cubicSymbol b h‖^2) ≤
        C*B^(1/3:ℝ)*(coreDyadicConductor i j)^(-(1/4:ℝ))*N*
          ∑ b ∈ S, ‖β b‖^2 := by
  obtain ⟨C₁,C₂,hC₁,hC₂,hraw⟩ := noncube_three_sieve_bounds hHuxley
    (by norm_num : (0:ℝ) < 1/12)
  let R := nonzeroNormBall 729
  have hR : 0 < (R.card:ℝ) := by
    apply Nat.cast_pos.mpr
    exact Finset.card_pos.mpr ⟨1,mem_nonzeroNormBall.mpr ⟨by norm_num [norm_one_eq],one_ne_zero⟩⟩
  refine ⟨288*R.card*C₂,by positivity,?_⟩
  intro S H β N B i j hN hB hS hsize hH
  let U := 2*(2:ℝ)^i
  let V := 2*(2:ℝ)^j
  let D := coreDyadicConductor i j
  let J := coreDyadicCubeFactors B i j
  have hU : 1 ≤ U := by dsimp [U]; nlinarith [one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n := i)]
  have hV : 1 ≤ V := by dsimp [V]; nlinarith [one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n := j)]
  have hD : 0 < D := coreDyadicConductor_pos i j
  have hUV : U*V ≤ 8*D := by
    have hh : U*V ≤ U*V^2 := mul_le_mul_of_nonneg_left (by nlinarith) (by linarith)
    have he : U*V^2 = 8*D := by dsimp [U,V,D,coreDyadicConductor]; ring
    exact hh.trans_eq he
  have hST (n : ℕ) : ∀ s ∈ squarefreePrimaryDyad n,
      primary s ∧ Squarefree s ∧ norm s ≤ 2*(2:ℝ)^n := by
    intro s hs
    have hg := squarefreePrimaryDyad_gramDyad hs
    exact ⟨hg.1,hg.2.1,hg.2.2.2.le⟩
  have hraw' := hraw S R (squarefreePrimaryDyad i) (squarefreePrimaryDyad j) J H
    N U V hN hU hV hS (hST i) (hST j) hH β
  have hE : 0 ≤ ∑ b ∈ S, ‖β b‖^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have ho := hraw'.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hE)
  have hweight : (J.card:ℝ)*D^(1/3:ℝ) ≤ 18*B^(1/3:ℝ) :=
    coreDyadicCubeFactors_card_weight hB i j
  have hpow : (U*V)^(1/12:ℝ) ≤ 8*D^(1/12:ℝ) := by
    calc
      _ ≤ (8*D)^(1/12:ℝ) := Real.rpow_le_rpow (by positivity) hUV (by norm_num)
      _ = (8:ℝ)^(1/12:ℝ)*D^(1/12:ℝ) := Real.mul_rpow (by norm_num) hD.le
      _ ≤ _ := mul_le_mul_of_nonneg_right
        ((Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 8) (by norm_num : (1/12:ℝ) ≤ 1)).trans_eq (Real.rpow_one 8))
        (Real.rpow_nonneg hD.le _)
  have hscalar : (J.card:ℝ)*(U*V)^(1/12:ℝ) ≤
      144*B^(1/3:ℝ)*D^(-(1/4:ℝ)) := by
    calc
      _ ≤ (J.card:ℝ)*(8*D^(1/12:ℝ)) := mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _)
      _ = 8*((J.card:ℝ)*D^(1/3:ℝ))*D^(-(1/4:ℝ)) := by
        rw [show (1/12:ℝ) = 1/3+ -(1/4) by norm_num,Real.rpow_add hD]
        ring
      _ ≤ 8*(18*B^(1/3:ℝ))*D^(-(1/4:ℝ)) := by gcongr
      _ = _ := by ring
  have hsize' : (U*V)^2+N ≤ 2*N := by
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ U*V) hUV 2
    linarith
  calc
    _ ≤ ((R.card:ℝ)*C₂)*((J.card:ℝ)*(U*V)^(1/12:ℝ))*((U*V)^2+N)*
        ∑ b ∈ S, ‖β b‖^2 := by convert ho using 1; ring
    _ ≤ ((R.card:ℝ)*C₂)*(144*B^(1/3:ℝ)*D^(-(1/4:ℝ)))*(2*N)*
        ∑ b ∈ S, ‖β b‖^2 := by gcongr
    _ = _ := by dsimp [D,R]; ring

end CubicFirstMoment

end

end OAI
