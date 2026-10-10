import Mathlib
import OAI.Probability.LogConcave.Sampling.Reindex

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators ENNReal NNReal

lemma normalizedTensorMajorant_order_budget {a : ℝ} (ha : 0<a) (ha1 : a≤1)
    (e n : ℕ) (hn : n≤e+2) :
    normalizedTensorMajorant n a≤
      (40*((e:ℝ)+3))^(12*(e+1))*((Real.sqrt a)⁻¹)^e := by
  have hR : 1≤(Real.sqrt a)⁻¹ := (one_le_inv₀ (Real.sqrt_pos.mpr ha)).mpr
    (by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt ha1)
  have hB : 1≤40*((e:ℝ)+3) := by nlinarith [Nat.cast_nonneg (α:=ℝ) e]
  apply (normalizedTensorMajorant_le ha n).trans
  apply mul_le_mul
  · apply (pow_le_pow_left₀ (by positivity : 0≤10*((n:ℝ)+1))
      (show 10*((n:ℝ)+1)≤40*((e:ℝ)+3) by
        have hn' : (n:ℝ)≤(e:ℝ)+2 := by exact_mod_cast hn
        nlinarith [Nat.cast_nonneg (α:=ℝ) e]) _).trans
    exact pow_le_pow_right₀ hB (by omega)
  · exact pow_le_pow_right₀ hR (by omega)
  · positivity
  · positivity

def normalizedScoreMajorant (e : ℕ) (a : ℝ) : ℝ :=
  2+normalizedTensorMajorant (e+2) a+normalizedTensorMajorant (e+1) a

lemma normalizedScoreMajorant_nonneg (e : ℕ) (a : ℝ) : 0≤normalizedScoreMajorant e a :=
  add_nonneg (add_nonneg (by norm_num) (normalizedTensorMajorant_nonneg _ _))
    (normalizedTensorMajorant_nonneg _ _)

lemma normalizedScoreMajorant_budget {a : ℝ} (ha : 0<a) (ha1 : a≤1) (e : ℕ) :
    normalizedScoreMajorant e a≤
      (40*((e:ℝ)+3))^(16*(e+1))*((Real.sqrt a)⁻¹)^e := by
  let B : ℝ := 40*((e:ℝ)+3)
  let R : ℝ := (Real.sqrt a)⁻¹
  have hB : 4≤B := by dsimp [B]; nlinarith [Nat.cast_nonneg (α:=ℝ) e]
  have hB1 : 1≤B := by linarith
  have hR : 1≤R := (one_le_inv₀ (Real.sqrt_pos.mpr ha)).mpr
    (by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt ha1)
  have hP : 1≤B^(12*(e+1))*R^e := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hB1) (one_le_pow₀ hR)
  have hn1 := normalizedTensorMajorant_order_budget ha ha1 e (e+2) le_rfl
  have hn2 := normalizedTensorMajorant_order_budget ha ha1 e (e+1) (by omega)
  change normalizedScoreMajorant e a≤B^(16*(e+1))*R^e
  calc
    _ ≤ 4*(B^(12*(e+1))*R^e) := by dsimp [normalizedScoreMajorant]; linarith
    _ ≤ B*(B^(12*(e+1))*R^e) := mul_le_mul_of_nonneg_right hB (by positivity)
    _ = B^(12*(e+1)+1)*R^e := by rw [pow_succ]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hB1 (by omega)) (by positivity)

def physicalTameScore {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) :
    TameScore (interpolationPotential F x r ρ) (ENNReal.ofReal ((Real.sqrt (1-ρ^2))⁻¹)) where
  bound e := normalizedScoreMajorant e (1-ρ^2)
  nonneg e := normalizedScoreMajorant_nonneg e _
  hessian e y := by
    apply (scorePosition_allSplit hF x hr hlam hl hρ0 hρ1 e y).mono
    · exact add_nonneg (by split_ifs <;> norm_num) (normalizedTensorMajorant_nonneg _ _)
    · dsimp [normalizedScoreMajorant]
      have := normalizedTensorMajorant_nonneg (e+1) (1-ρ^2)
      split_ifs <;> linarith
  spatial e he y := by
    apply (scoreField_spatial_allSplit hF x hr hlam hl hρ0 hρ1 e he y).mono
    · exact add_nonneg (by norm_num) (normalizedTensorMajorant_nonneg _ _)
    · dsimp [normalizedScoreMajorant]
      have := normalizedTensorMajorant_nonneg (e+2) (1-ρ^2)
      linarith
  budget e := by
    have ha : 0<1-ρ^2 := (probability_time hρ0 hρ1).1
    have hh := ENNReal.ofReal_le_ofReal (normalizedScoreMajorant_budget ha (by nlinarith [sq_nonneg ρ]) e)
    have he : ENNReal.ofReal (40*((e:ℝ)+3))=40*((e:ℝ≥0∞)+3) := by
      norm_cast
    rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_pow (by positivity),he,
      ENNReal.ofReal_pow (by positivity)] at hh
    exact hh

end LogConcaveSampling

end

end

end

end OAI
