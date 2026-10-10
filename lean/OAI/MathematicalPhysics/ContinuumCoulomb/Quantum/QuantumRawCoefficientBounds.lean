import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRawCompiler

namespace OAI

/-! Uniform bounds for the actual rational four-spin coefficients. The
sampling precision does not enter these bounds. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAxisSample

theorem fieldValue_abs (k : ℕ) (a : Fin 2) (t : ℚ) (e : Fin 3) :
    |(fieldValue k a t e:ℝ)| ≤ 65*|(t:ℝ)| := by
  have h := (abs_sub_abs_le_abs_sub (fieldValue k a t e:ℝ)
    (qmaFieldEdgeWeight a (t:ℝ) e)).trans (fieldValue_error k a t e)
  have hw := qmaFieldEdgeWeight_bound a (t:ℝ) e
  have hp : (2:ℝ)⁻¹^k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hm := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 64*|(t:ℝ)|)
  linarith

theorem crossValue_abs (k : ℕ) (r : ℚ) (a b : Fin 2) (t : ℚ) (p q : Fin 4) :
    |(crossValue k r a b t p q:ℝ)| ≤ 3920*|(r:ℝ)| *(1+|(t:ℝ)|) := by
  have hs : |(stencil a true p:ℝ)| * |(stencil b (decide (t≤0)) q:ℝ)| ≤ 784 := by
    rw [stencil_cast,stencil_cast]
    exact (mul_le_mul (qmaFourAxisWeights_pointwise a true p)
      (qmaFourAxisWeights_pointwise b _ q) (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
  simp only [crossValue,Rat.cast_mul,abs_mul]
  calc
    _ ≤ (|(r:ℝ)| *(5*(1+|(t:ℝ)|)))*784 :=
      mul_le_mul (mul_le_mul_of_nonneg_left (calibrated_bound a b k t) (abs_nonneg _)) hs
        (by positivity) (by positivity)
    _ = _ := by ring

theorem shiftValue_abs (a : Fin 2) (t : ℚ) : |(shiftValue a t:ℝ)| ≤ |(t:ℝ)| := by
  by_cases h : a=0
  · simp [shiftValue,h]
  · simp only [shiftValue,h,ite_false,Rat.cast_div,Rat.cast_ofNat,abs_div]
    norm_num

theorem offset_abs (k : ℕ) (a b : Fin 2) (t : ℚ) :
    |(offset k a b t:ℝ)| ≤ 685600*|(t:ℝ)| := by
  have h := (abs_sub_abs_le_abs_sub (offset k a b t:ℝ)
    (qmaFourEnergyOffset a b (t:ℝ))).trans (offset_error k a b t)
  have hw := qmaFourEnergyOffset_bound a b (t:ℝ)
  have hp : (2:ℝ)⁻¹^k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hm := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 320800*|(t:ℝ)|)
  linarith

end ContinuumCoulomb.QuantumAxisSample

end

end OAI
