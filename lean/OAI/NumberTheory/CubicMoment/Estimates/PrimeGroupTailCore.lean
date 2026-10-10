import OAI.NumberTheory.CubicMoment.Estimates.PrimeGroupTailSieve
import OAI.NumberTheory.CubicMoment.Estimates.CoreBlockGeometry

namespace OAI

/-! Small-B conductor bounds on the actual ramified/cube/squarefree blocks.
All coefficients remain arbitrary and the cube multiplicity is summed. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem primeGroupTail_core_block_sieve (hHuxley : HuxleyAdditiveLargeSieve)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S H : Finset Eisenstein) (β : Eisenstein → ℂ)
      (N B : ℝ) (i j : ℕ), 1 ≤ N → 0 ≤ B →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ norm b ≤ N) →
      8*coreDyadicConductor i j ≤ N^(19/20:ℝ) →
      H ⊆ coreDyadicBlock B i j →
      (∑ h ∈ H, ‖∑ b ∈ S, β b*cubicSymbol b h‖^2) ≤
        C*N^(2*ε)*B^(1/3:ℝ)*
          (N/(coreDyadicConductor i j)^(1/3:ℝ)+N^(119/120:ℝ))*∑ b ∈ S, ‖β b‖^2 := by
  obtain ⟨C,hC,hbound⟩ := primeGroupTail_frequency_sieve hHuxley hε
  let K : ℝ := (nonzeroNormBall 729).card
  have hK : 0 < K := by
    apply Nat.cast_pos.mpr
    apply Finset.card_pos.mpr
    exact ⟨1,mem_nonzeroNormBall.mpr ⟨by norm_num [norm_one_eq],one_ne_zero⟩⟩
  refine ⟨108*K*C,by positivity,?_⟩
  intro S H β N B i j hN hB hS hD hH
  have hU : 1 ≤ 2*(2:ℝ)^i := by nlinarith [one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n := i)]
  have hV : 1 ≤ 2*(2:ℝ)^j := by nlinarith [one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n := j)]
  have hST (n : ℕ) : ∀ s ∈ squarefreePrimaryDyad n,
      primary s ∧ Squarefree s ∧ norm s ≤ 2*(2:ℝ)^n := by
    intro s hs
    have hg := squarefreePrimaryDyad_gramDyad hs
    exact ⟨hg.1,hg.2.1,hg.2.2.2.le⟩
  have hcard : ((squarefreePrimaryDyad j).card:ℝ) ≤ 18*(2*(2:ℝ)^j) :=
    primary_support_card_le (squarefreePrimaryDyad j) (by positivity)
      (fun s hs => ⟨(hST j s hs).1,(hST j s hs).2.2⟩)
  have hD' : (2*(2:ℝ)^i)*(2*(2:ℝ)^j)^2 = 8*coreDyadicConductor i j := by
    unfold coreDyadicConductor
    ring
  have hh := hbound S (nonzeroNormBall 729) (squarefreePrimaryDyad i)
    (squarefreePrimaryDyad j) (coreDyadicCubeFactors B i j) H N
    (2*(2:ℝ)^i) (2*(2:ℝ)^j) hN hU hV (by rwa [hD']) hS (hST i) (hST j) hcard hH β
  rw [hD',Real.mul_rpow (by norm_num : (0:ℝ) ≤ 8) (coreDyadicConductor_pos i j).le,
    rpow_eight_third] at hh
  let D := (coreDyadicConductor i j)^(1/3:ℝ)
  have hDp : 0 < D := Real.rpow_pos_of_pos (coreDyadicConductor_pos i j) _
  have hweight : ((coreDyadicCubeFactors B i j).card:ℝ)*D ≤ 18*B^(1/3:ℝ) :=
    coreDyadicCubeFactors_card_weight hB i j
  have hfirst : ((coreDyadicCubeFactors B i j).card:ℝ)*N ≤ 18*B^(1/3:ℝ)*(N/D) := by
    have hc : ((coreDyadicCubeFactors B i j).card:ℝ) ≤ 18*B^(1/3:ℝ)/D :=
      (le_div_iff₀ hDp).mpr hweight
    convert mul_le_mul_of_nonneg_right hc (zero_le_one.trans hN) using 1
    ring
  have hsecond := mul_le_mul_of_nonneg_right hweight (show 0 ≤ 6*N^(119/120:ℝ) by positivity)
  have htotal : ((coreDyadicCubeFactors B i j).card:ℝ)*(N+3*N^(119/120:ℝ)*(2*D)) ≤
      108*B^(1/3:ℝ)*(N/D+N^(119/120:ℝ)) := by
    have hx : 0 ≤ B^(1/3:ℝ)*(N/D) := by positivity
    nlinarith [hfirst,hsecond]
  apply hh.trans
  have hE : 0 ≤ ∑ b ∈ S, ‖β b‖^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left htotal (show 0 ≤ K*C*N^(2*ε) by positivity)) hE
  convert hm using 1 <;> dsimp [K,D] <;> ring

end CubicFirstMoment

end

end OAI
