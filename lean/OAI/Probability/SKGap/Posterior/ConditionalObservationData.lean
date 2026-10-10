import Mathlib
import OAI.Probability.SKGap.Localization.EmpiricalConditionalData

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.Frobenius

lemma scalarA_empirical_sum {n : ℕ} [NeZero n] (j t σ : ℝ) (y : Fin n → ℝ) :
    ∑ i,tanh (y i)*(y i-scalarD j (empiricalLaw y,t,σ))=
      (n:ℝ)*scalarA j (empiricalLaw y,t,σ) := by
  simp only [scalarA,scalarM,integral_empiricalLaw,Fintype.card_fin]
  have hn : (n:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  rw [mul_sub,← mul_assoc,mul_inv_cancel₀ hn,one_mul]
  simp only [mul_sub]
  rw [Finset.sum_sub_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _; ring
  · rw [← Finset.sum_mul]
    field_simp

lemma empirical_unit_scale {n : ℕ} [NeZero n] (y : Fin n → ℝ) {q : ℝ} (hq : 0 < q) :
    sqrt ((n:ℝ)*q) • (empiricalUnit y q).ofLp=(fun i=>tanh (y i)) := by
  have hc : sqrt ((n:ℝ)*q) ≠ 0 := ne_of_gt (sqrt_pos.mpr (mul_pos (by exact_mod_cast NeZero.pos n) hq))
  ext i
  simp only [empiricalUnit,WithLp.ofLp_toLp,Pi.smul_apply,smul_eq_mul]
  field_simp

lemma empirical_Z_formula {n : ℕ} [NeZero n] (y : Fin n → ℝ) (d : ℝ) {s : ℝ} (hs : 0 < s) :
    sqrt s • (empiricalGramColumns y d s 2).ofLp=(fun i=>(y i-d)/(sqrt (n:ℝ)*sqrt s)) := by
  have hn : sqrt (n:ℝ) ≠ 0 := ne_of_gt (sqrt_pos.mpr (by exact_mod_cast NeZero.pos n))
  have hss : sqrt s ≠ 0 := (sqrt_pos.mpr hs).ne'
  ext i
  simp only [empiricalGramColumns,gramCoordinates,Matrix.cons_val,Pi.smul_apply,
    WithLp.ofLp_toLp,smul_eq_mul]
  field_simp
  rw [Real.sq_sqrt hs.le]
  ring

lemma empirical_unit_center_dot {n : ℕ} [NeZero n] (j t σ : ℝ) (y : Fin n → ℝ) :
    (empiricalUnit y (scalarQMoment (empiricalLaw y))).ofLp⬝ᵥ
      (fun i=>y i-scalarD j (empiricalLaw y,t,σ))=
    (n:ℝ)*scalarA j (empiricalLaw y,t,σ)/sqrt ((n:ℝ)*scalarQMoment (empiricalLaw y)) := by
  simp only [empiricalUnit,WithLp.ofLp_toLp,dotProduct,div_mul_eq_mul_div,← Finset.sum_div]
  rw [scalarA_empirical_sum]

lemma empirical_unit_observation_dot {n : ℕ} [NeZero n] (j t σ B : ℝ)
    (y : Fin n → ℝ) (hq : 0 < scalarQMoment (empiricalLaw y)) :
    (empiricalUnit y (scalarQMoment (empiricalLaw y))).ofLp⬝ᵥ
      (fun i=>y i-scalarD j (empiricalLaw y,t,σ)+B*tanh (y i))=
    (n:ℝ)*(scalarA j (empiricalLaw y,t,σ)+B*scalarQMoment (empiricalLaw y))/
      sqrt ((n:ℝ)*scalarQMoment (empiricalLaw y)) := by
  let q := scalarQMoment (empiricalLaw y)
  let u := (empiricalUnit y q).ofLp
  let c := sqrt ((n:ℝ)*q)
  have hc : c ≠ 0 := ne_of_gt (sqrt_pos.mpr (mul_pos (by exact_mod_cast NeZero.pos n) hq))
  have hc2 : c^2=(n:ℝ)*q := sq_sqrt (mul_nonneg (Nat.cast_nonneg n) hq.le)
  have hu : u⬝ᵥu=1 := empiricalUnit_unit y hq
  have hscale : c • u=(fun i=>tanh (y i)) := empirical_unit_scale y hq
  have heq : (fun i=>y i-scalarD j (empiricalLaw y,t,σ)+B*tanh (y i))=
      (fun i=>y i-scalarD j (empiricalLaw y,t,σ))+B • (c • u) := by
    rw [hscale]; rfl
  rw [heq,dotProduct_add,dotProduct_smul,dotProduct_smul,hu,empirical_unit_center_dot]
  simp only [smul_eq_mul,mul_one]
  change (n:ℝ)*scalarA j (empiricalLaw y,t,σ)/c+B*c=(n:ℝ)*(scalarA j (empiricalLaw y,t,σ)+B*q)/c
  field_simp
  linear_combination B*hc2
end SKGap
end
end

end OAI
