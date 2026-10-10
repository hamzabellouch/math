import OAI.Probability.SATComputability.ArithmeticConstructors
import OAI.MathematicalPhysics.RapidForcing.BoundsPrograms

namespace OAI

namespace FixedClauseThreshold.Computability.FiniteArithmetic

open Nat.Partrec RapidForcing.EffectiveArithmetic RapidForcing.EffectiveProfile
local instance weightedExpressionsRatPrimcodable : Primcodable ℚ := PeriodicLattice.RecursiveArithmetic.ratPrimcodable

private theorem rational_abs_le_num (q : ℚ) : |(q : ℝ)| ≤ (q.num.natAbs : ℝ) := by
  have hd : (1 : ℝ) ≤ q.den := by exact_mod_cast q.pos
  have he : (q : ℝ) = (q.num : ℝ) / q.den := by
    conv_lhs => rw [← Rat.num_div_den q]
    push_cast
    rfl
  rw [he, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ q.den)]
  calc
    |(q.num : ℝ)| / q.den ≤ |(q.num : ℝ)| :=
      div_le_self (abs_nonneg _) hd
    _ = (q.num.natAbs : ℝ) := by simp

noncomputable def expressionBound (e : Code) : ℕ :=
  (expressionBall e 0).center.num.natAbs + (expressionBall e 0).radius.num.natAbs

attribute [local irreducible] expressionBall

@[fun_prop] theorem expressionBound_computable : Computable expressionBound := by
  have hb : Computable (fun e : Code => expressionBall e 0) :=
    Computable.comp (f := fun p : Code × ℕ => expressionBall p.1 p.2)
      (g := fun e : Code => (e, (0 : ℕ))) expressionBall_computable
      (Computable.id.pair (Computable.const 0))
  have hf : Computable (fun b : Ball => b.center.num.natAbs + b.radius.num.natAbs) := by
    fun_prop
  exact hf.comp hb

theorem expressionBound_valid (e : Code) : |expressionValue e| ≤ expressionBound e := by
  have h := (expressionBall_encloses e).1 0
  have hr := rational_abs_le_num (expressionBall e 0).radius
  have hc := rational_abs_le_num (expressionBall e 0).center
  have hrad : ((expressionBall e 0).radius : ℝ) ≤
      |((expressionBall e 0).radius : ℝ)| := le_abs_self _
  change _ ≤ (((expressionBall e 0).center.num.natAbs +
    (expressionBall e 0).radius.num.natAbs : ℕ) : ℝ)
  push_cast
  have ht := abs_add_le (expressionValue e - ((expressionBall e 0).center : ℝ))
    ((expressionBall e 0).center : ℝ)
  rw [sub_add_cancel] at ht
  have h' : |expressionValue e - ((expressionBall e 0).center : ℝ)| ≤
      ((expressionBall e 0).radius : ℝ) := by simpa only [Ball.Covers, abs_sub_comm] using h
  linarith

noncomputable def mixtureBound (bs : List (ℚ × Code)) : ℕ :=
  (bs.map (fun b => expressionBound b.2)).sum

noncomputable def mixtureExpression (bs : List (ℚ × Code)) : Code :=
  sumExpressions (bs.map (fun b => .comp (rationalExpression b.1) (exponentialExpression b.2)))

noncomputable def logMixtureExpression (bs : List (ℚ × Code)) : Code :=
  scaledLogExpression ((3 : ℚ)^mixtureBound bs)⁻¹ (mixtureExpression bs)

@[fun_prop] theorem mixtureBound_computable : Computable mixtureBound := by
  unfold mixtureBound
  apply (computable_list_sum (by fun_prop : Computable (fun p : ℕ × ℕ => p.1+p.2))).comp
  apply computable_list_map Computable.id
  unfold Computable₂
  fun_prop

@[fun_prop] theorem mixtureExpression_computable : Computable mixtureExpression := by
  unfold mixtureExpression
  apply sumExpressions_computable.comp
  apply computable_list_map Computable.id
  unfold Computable₂
  unfold exponentialExpression
  fun_prop

@[fun_prop] theorem logMixtureExpression_computable : Computable logMixtureExpression := by
  unfold logMixtureExpression scaledLogExpression positiveLogExpression
  fun_prop

theorem mixtureExpression_value (bs : List (ℚ × Code)) :
    expressionValue (mixtureExpression bs) =
      (bs.map (fun b => (b.1 : ℝ)*Real.exp (expressionValue b.2))).sum := by
  simp only [mixtureExpression, sumExpressions_value, List.map_map, Function.comp_def,
    expressionValue, rationalExpression_value, exponentialExpression_value]

private theorem small_exp_lower (N : ℕ) :
    ((3 : ℝ)^N)⁻¹ ≤ Real.exp (-(N : ℝ)) := by
  rw [Real.exp_neg, show Real.exp (N : ℝ) = (Real.exp 1)^N by
    rw [← Real.exp_nat_mul]; simp]
  apply inv_anti₀ (pow_pos (Real.exp_pos 1) N)
  exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le N

theorem logMixtureExpression_value (bs : List (ℚ × Code))
    (hw : ∀ b ∈ bs, 0 ≤ b.1) (hs : (bs.map Prod.fst).sum = 1) :
    expressionValue (logMixtureExpression bs) =
      Real.log ((bs.map (fun b => (b.1 : ℝ)*Real.exp (expressionValue b.2))).sum) := by
  have hB (b : ℚ × Code) (hb : b ∈ bs) :
      -(mixtureBound bs : ℝ) ≤ expressionValue b.2 := by
    have hle : expressionBound b.2 ≤ mixtureBound bs :=
      List.single_le_sum (fun (x : ℕ) _ => Nat.zero_le x) _
        (List.mem_map.mpr ⟨b, hb, rfl⟩)
    have hcast : (expressionBound b.2 : ℝ) ≤ mixtureBound bs := by exact_mod_cast hle
    have he := (abs_le.mp (expressionBound_valid b.2)).1
    linarith
  have hsum : (bs.map (fun b => (b.1 : ℝ))).sum = 1 := by
    have h := congrArg (fun q : ℚ => (q : ℝ)) hs
    simpa only [Rat.cast_one, Rat.cast_list_sum, List.map_map, Function.comp_def] using h
  have he : ((3 : ℝ)^mixtureBound bs)⁻¹ ≤
      (bs.map (fun b => (b.1 : ℝ)*Real.exp (expressionValue b.2))).sum := by
    calc
      _ = (bs.map (fun b => (b.1 : ℝ)*((3 : ℝ)^mixtureBound bs)⁻¹)).sum := by
        rw [List.sum_map_mul_right, hsum, one_mul]
      _ ≤ _ := by
        apply List.sum_le_sum
        intro b hb
        exact mul_le_mul_of_nonneg_left
          ((small_exp_lower _).trans (Real.exp_le_exp.mpr (hB b hb)))
          (by exact_mod_cast hw b hb)
  unfold logMixtureExpression
  rw [scaledLogExpression_value, mixtureExpression_value]
  · positivity
  · exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  · simpa only [Rat.cast_inv, Rat.cast_pow, Rat.cast_ofNat, mixtureExpression_value] using he

end FixedClauseThreshold.Computability.FiniteArithmetic

end OAI
