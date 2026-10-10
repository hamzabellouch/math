import OAI.NumberTheory.CubicMoment.Estimates.CoreBlockGeometry
import OAI.NumberTheory.CubicMoment.Angular.AngularSmallConductorLogSaving

namespace OAI

/-! The intermediate small-conductor estimate applied to the actual
finite core blocks, including their ramified and cube multiplicities. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_small_core_block_log_saving (hHuxley : HuxleyAdditiveLargeSieve)
    {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    {R : ℝ} (hR : 1 ≤ R) (hlo : ∀ r i x, x < 1 → W r i x = 0)
    (hhi : ∀ r i x, R < x → W r i x = 0) (k : ℕ) :
    ∃ (C : ℝ) (A : ℕ), 0 < C ∧ ∀ (r : γ) (X : ι → ℝ) (B : ℝ) (i j : ℕ)
      (v e : Eisenstein) (u : ℝ) (H : Finset Eisenstein),
      1 ≤ L r → (∀ a, 1 ≤ X a) → (∏ a, X a) = L r → 0 ≤ B →
      (4*(2:ℝ)^i*(2:ℝ)^j)^2 ≤ L r →
      (1+Real.log (L r))^A ≤ 8*coreDyadicConductor i j →
      H ⊆ coreDyadicBlock B i j →
      (∑ h ∈ H, ‖fullStructuredAngularPrimeSum ℓ R h 1 v e u (W r) X‖^2) ≤
        C*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^k := by
  obtain ⟨C,A,hC,hbound⟩ := angular_small_conductor_log_saving ℓ hHuxley hW hR hlo hhi k
  let K := (nonzeroNormBall 729).card
  have hK : 0 < K := by
    apply Finset.card_pos.mpr
    refine ⟨1,mem_nonzeroNormBall.mpr ⟨?_,one_ne_zero⟩⟩
    norm_num [norm_one_eq]
  refine ⟨36*C*K,A,by dsimp [K]; positivity,?_⟩
  intro r X B i j v e u H hL hX hprod hB hsize hlarge hH
  have hU : 1 ≤ 2*(2:ℝ)^i := by nlinarith [one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n := i)]
  have hV : 1 ≤ 2*(2:ℝ)^j := by nlinarith [one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n := j)]
  have hD : (2*(2:ℝ)^i)*(2*(2:ℝ)^j)^2 = 8*coreDyadicConductor i j := by
    unfold coreDyadicConductor
    ring
  have hST (n : ℕ) : ∀ s ∈ squarefreePrimaryDyad n,
      primary s ∧ Squarefree s ∧ norm s ≤ 2*(2:ℝ)^n := by
    intro s hs
    have hg := squarefreePrimaryDyad_gramDyad hs
    exact ⟨hg.1,hg.2.1,hg.2.2.2.le⟩
  have hh := hbound r X (2*(2:ℝ)^i) (2*(2:ℝ)^j) v e u
    (nonzeroNormBall 729) (squarefreePrimaryDyad i) (squarefreePrimaryDyad j)
    (coreDyadicCubeFactors B i j) H hL hX hprod hU hV
    (by convert hsize using 1; ring) (by rwa [hD]) (hST i) (hST j) hH
  rw [hD] at hh
  apply hh.trans
  have hz : 0 ≤ (1+Real.log (L r))^k := pow_nonneg (by linarith [Real.log_nonneg hL]) _
  apply div_le_div_of_nonneg_right _ hz
  have hweight := coreDyadicCubeFactors_card_eight_weight hB i j
  have hm := mul_le_mul_of_nonneg_left hweight
    (mul_nonneg (mul_nonneg hC.le (Nat.cast_nonneg K)) (sq_nonneg (L r)))
  dsimp [K] at hm ⊢
  nlinarith [hm]

end CubicFirstMoment

end

end OAI
