import OAI.NumberTheory.CubicMoment.Estimates.NormalizedCoordinateMoments

namespace OAI

/-! The elementary power margins used to return from a global cutoff at
2Y to the original exceptional conductor neighborhoods. -/
noncomputable section
open Filter
namespace CubicFirstMoment

lemma twice_rpow_le_mul_rpow {Y e : ℝ} (hY : 0 ≤ Y) (he : 1 ≤ e) :
    2*Y^e ≤ (2*Y)^e := by
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hY]
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hY _)
  calc
    (2:ℝ) = 2^(1:ℝ) := (Real.rpow_one _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) he

lemma first_prime_error_rows {Y N κ c : ℝ} (hY : 1 ≤ Y) (hc : 0 < c)
    (hκ : κ ≤ c/256) (hN : N ≤ Y^(1+κ)) (a : Eisenstein) (ha : gramDyad N a) :
    primary a ∧ Squarefree a ∧ norm a ≤ (2*Y)^(1+c/256) := by
  refine ⟨ha.1,ha.2.1,?_⟩
  calc
    norm a ≤ 2*N := ha.2.2.2.le
    _ ≤ 2*Y^(1+κ) := by gcongr
    _ ≤ 2*Y^(1+c/256) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hY (by linarith)) (by norm_num)
    _ ≤ _ := twice_rpow_le_mul_rpow (by linarith) (by linarith)

lemma balanced_prime_error_rows {Y κ c : ℝ} (hY : 1 ≤ Y) (hc : 0 < c)
    (hκ : κ ≤ c/256) (a : Eisenstein × Eisenstein)
    (ha : PrimarySquarefreePair a ∧ norm a.1 ≤ Y^(1/3+κ) ∧
      norm a.2 ≤ Y^(1/3+κ) ∧ Y^(1/1000:ℝ) ≤ norm a.1) :
    PrimarySquarefreePair a ∧ norm a.1 ≤ (2*Y)^(1/3+c/256) ∧
      norm a.2 ≤ (2*Y)^(1/3+c/256) := by
  have hp : Y^(1/3+κ) ≤ (2*Y)^(1/3+c/256) :=
    (Real.rpow_le_rpow_of_exponent_le hY (by linarith)).trans
      (Real.rpow_le_rpow (by linarith) (by linarith) (by linarith))
  exact ⟨ha.1,ha.2.1.trans hp,ha.2.2.1.trans hp⟩

lemma absorb_prime_coordinate_error {e d C : ℝ} (he : 0 < e) (hd : 0 < d)
    (hC : 0 ≤ C) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ T : ℝ, 1 ≤ T ∧ ∀ Y : ℝ, T ≤ Y →
      2*Y^(7/3-e)+2*C*(2*Y)^(7/3-d) ≤ Y^(7/3-ε) := by
  let δ := min e d
  let K := 2+2*C*2^(7/3-d)
  have hδ : 0 < δ := lt_min he hd
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (show 0 < δ/2 by positivity)).eventually_ge_atTop K)
  refine ⟨δ/2,by positivity,max 1 T,le_max_left _ _,?_⟩
  intro Y hY
  have hY1 : 1 ≤ Y := (le_max_left _ _).trans hY
  have hYp : 0 < Y := zero_lt_one.trans_le hY1
  have h₁ : Y^(7/3-e) ≤ Y^(7/3-δ) :=
    Real.rpow_le_rpow_of_exponent_le hY1 (by dsimp [δ]; linarith [min_le_left e d])
  have h₂ : Y^(7/3-d) ≤ Y^(7/3-δ) :=
    Real.rpow_le_rpow_of_exponent_le hY1 (by dsimp [δ]; linarith [min_le_right e d])
  calc
    _ = 2*Y^(7/3-e)+(2*C*2^(7/3-d))*Y^(7/3-d) := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hYp.le]
      ring
    _ ≤ 2*Y^(7/3-δ)+(2*C*2^(7/3-d))*Y^(7/3-δ) := by gcongr
    _ = K*Y^(7/3-δ) := by dsimp [K]; ring
    _ ≤ Y^(δ/2)*Y^(7/3-δ) := mul_le_mul_of_nonneg_right
      (hT Y ((le_max_right _ _).trans hY)) (Real.rpow_nonneg hYp.le _)
    _ = _ := by rw [← Real.rpow_add hYp]; congr 1; ring

end CubicFirstMoment

end

end OAI
