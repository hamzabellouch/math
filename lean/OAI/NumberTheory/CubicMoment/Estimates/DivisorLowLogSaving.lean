import OAI.NumberTheory.CubicMoment.Estimates.DivisorLowHeightBlocks
import OAI.NumberTheory.CubicMoment.Estimates.LowHeightBracketLog

namespace OAI

/-! The actual noncube coprimality mass at polylogarithmic height. No
small norm power is lost when the divisor rows are summed. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem divisor_noncube_low_log_saving (hpnt : PrimaryPrimePNT)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) (k : ℕ) :
    ∃ (K : ℝ) (Ct : ℕ), 0 < K ∧ ∀ (S H U : Finset Eisenstein) (β : Eisenstein → ℂ)
      (Z : ℕ) (B T M u : ℝ), 65536 ≤ (Z:ℝ) → 1 ≤ B → 0 ≤ M →
      (1+Real.log Z)^Ct ≤ T → (∀ p ∈ U, primaryPrime p) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ norm b ≤ (Z:ℝ)) →
      (∀ b ∈ S, ‖β b‖ ≤ M) → 8*B ≤ (Z:ℝ)^(3/4:ℝ) →
      (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B ∧ ¬∃ a : Eisenstein, a^3 = h) →
      dyadicHeightMean (fun t => divisorCharacterMass S H U β (t+u)) T ≤
        K*M^2*(Z:ℝ)^2*B^(1/3:ℝ)/(1+Real.log Z)^k := by
  obtain ⟨K,hK,hbound⟩ := divisor_noncube_low_height_blocks hMV hC hHuxley
  obtain ⟨Ke,d,hKe,he⟩ := bounded_third_divisor_energy hpnt
  obtain ⟨Kb,Ct,hKb,hbracket⟩ := low_height_bracket_log_saving (k+d)
  refine ⟨K*Ke*Kb,Ct,by positivity,?_⟩
  intro S H U β Z B T M u hZ hB hM hT hU hS hβ hsize hH
  let N : ℝ := Z
  let L := 1+Real.log N
  let V := 5832*L^(4*(k+d+2))
  let A := (1+N/T)*V+((largeCoreDyadicIndices V B).card:ℝ)*
    (N*(V/5832)^(-(1/4:ℝ))+N^(1-1/20000:ℝ))
  have hN1 : 1 ≤ N := by dsimp [N]; linarith
  have hNp : 0 < N := zero_lt_one.trans_le hN1
  have hL1 : 1 ≤ L := by dsimp [L]; linarith [Real.log_nonneg hN1]
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  have hTp : 0 < T := (pow_pos hLp _).trans_le hT
  have hV : 0 < V := by dsimp [V]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hBN : B ≤ N^2 := by
    calc
      B ≤ 8*B := by linarith
      _ ≤ N^(3/4:ℝ) := hsize
      _ ≤ N^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
      _ = _ := Real.rpow_two N
  have hs := hbracket N B T hZ hB hBN hT
  have hexp : Real.exp 1 ≤ N := by
    have hh : Real.exp (1:ℝ) < 3 := Real.exp_one_lt_d9.trans_le (by norm_num)
    dsimp [N]
    linarith
  have henergy := he S β N M hexp hM hS hβ
  have hb := hbound S H U β Z B V T u hZ (zero_le_one.trans hB) hV hTp hU hS hsize hH
  calc
    _ ≤ K*B^(1/3:ℝ)*(Ke*M^2*N*L^d)*A := hb.trans (by gcongr)
    _ = (K*Ke*M^2*B^(1/3:ℝ)*L^d)*(N*A) := by ring
    _ ≤ (K*Ke*M^2*B^(1/3:ℝ)*L^d)*(Kb*N^2/L^(k+d)) := by
      apply mul_le_mul_of_nonneg_left hs
      positivity
    _ = _ := by
      rw [pow_add]
      field_simp
      ring

end CubicFirstMoment

end

end OAI
