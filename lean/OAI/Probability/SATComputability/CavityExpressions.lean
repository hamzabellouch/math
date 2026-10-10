import OAI.Probability.SATComputability.PhysicalExpressions
import OAI.Probability.DilutedSpin.CavityBounds

namespace OAI

namespace FixedClauseThreshold.Computability.FiniteArithmetic

open Nat.Partrec DilutedSpinGlass RapidForcing.EffectiveArithmetic
open scoped BigOperators
local instance cavityExpressionsRatPrimcodable : Primcodable ℚ := PeriodicLattice.RecursiveArithmetic.ratPrimcodable

noncomputable def boltzmannAtom {p : ℕ} (θ : ℚ) (xs : Fin p → Code)
    (s : Fin p → Bool) : Code :=
  .pair (rationalExpression θ)
    (sumExpressions (List.ofFn (fun i => logQExpression (xs i) (s i))))

@[fun_prop] theorem boltzmannAtom_computable (p : ℕ) :
    Computable (fun a : ℚ × (Fin p → Code) × (Fin p → Bool) =>
      boltzmannAtom a.1 a.2.1 a.2.2) := by
  have hv : Computable (fun a : ℚ × (Fin p → Code) × (Fin p → Bool) =>
      List.ofFn (fun i => logQExpression (a.2.1 i) (a.2.2 i))) := by
    apply Computable.list_ofFn
    intro i
    fun_prop
  unfold boltzmannAtom
  fun_prop

theorem exp_boltzmannAtom {p : ℕ} (θ : ℚ) (xs : Fin p → Code) (s : Fin p → Bool) :
    Real.exp (expressionValue (boltzmannAtom θ xs s)) =
      Real.exp (θ : ℝ) * ∏ i, q (expressionValue (xs i)) (s i) := by
  simp only [boltzmannAtom, expressionValue, rationalExpression_value,
    sumExpressions_value, List.map_ofFn, List.sum_ofFn, Function.comp_def,
    Real.exp_add, Real.exp_sum, exp_logQExpression]

def clausePenalty (β : ℚ) (J s : Fin 3 → Bool) : ℚ :=
  if ∀ i, s i ≠ J i then -β else 0

@[fun_prop] theorem clausePenalty_computable :
    Computable (fun p : ℚ × (Fin 3 → Bool) × (Fin 3 → Bool) =>
      clausePenalty p.1 p.2.1 p.2.2) := by
  have h : Computable (fun p : ℚ × (Fin 3 → Bool) × (Fin 3 → Bool) =>
      if p.2.2 0 ≠ p.2.1 0 ∧ p.2.2 1 ≠ p.2.1 1 ∧ p.2.2 2 ≠ p.2.1 2
      then -p.1 else 0) := by fun_prop
  exact h.of_eq (fun p => by simp [clausePenalty, Fin.forall_fin_succ])

theorem clausePenalty_cast (β : ℚ) (J s : Fin 3 → Bool) :
    (clausePenalty β J s : ℝ) = satInteraction (β : ℝ) J s := by
  unfold clausePenalty satInteraction
  split <;> simp

theorem sum_bool_vector_succ {p : ℕ} (f : (Fin (p+1) → Bool) → ℝ) :
    (∑ s, f s) =
      (∑ t : Fin p → Bool, f (Fin.cons false t)) +
      ∑ t : Fin p → Bool, f (Fin.cons true t) := by
  rw [← (Fin.consEquiv (fun _ : Fin (p+1) => Bool)).sum_comp, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  exact add_comm _ _

noncomputable def edgeExpression (β : ℚ) (J : Fin 3 → Bool) (xs : Fin 3 → Code) : Code :=
  binaryLogSumExpression
    (binaryLogSumExpression
      (binaryLogSumExpression (boltzmannAtom (clausePenalty β J ![false,false,false]) xs ![false,false,false])
        (boltzmannAtom (clausePenalty β J ![false,false,true]) xs ![false,false,true]))
      (binaryLogSumExpression (boltzmannAtom (clausePenalty β J ![false,true,false]) xs ![false,true,false])
        (boltzmannAtom (clausePenalty β J ![false,true,true]) xs ![false,true,true])))
    (binaryLogSumExpression
      (binaryLogSumExpression (boltzmannAtom (clausePenalty β J ![true,false,false]) xs ![true,false,false])
        (boltzmannAtom (clausePenalty β J ![true,false,true]) xs ![true,false,true]))
      (binaryLogSumExpression (boltzmannAtom (clausePenalty β J ![true,true,false]) xs ![true,true,false])
        (boltzmannAtom (clausePenalty β J ![true,true,true]) xs ![true,true,true])))

@[fun_prop] theorem edgeExpression_computable :
    Computable (fun p : ℚ × (Fin 3 → Bool) × (Fin 3 → Code) =>
      edgeExpression p.1 p.2.1 p.2.2) := by
  unfold edgeExpression
  fun_prop

theorem exp_edgeExpression (β : ℚ) (J : Fin 3 → Bool) (xs : Fin 3 → Code) :
    Real.exp (expressionValue (edgeExpression β J xs)) =
      edge (satInteraction (β : ℝ) J) (fun i => expressionValue (xs i)) := by
  unfold edgeExpression edge
  simp only [exp_binaryLogSumExpression, exp_boltzmannAtom, clausePenalty_cast]
  rw [sum_bool_vector_succ]
  simp_rw [sum_bool_vector_succ]
  simp only [Fintype.sum_unique]
  rfl

theorem edgeExpression_value (β : ℚ) (J : Fin 3 → Bool) (xs : Fin 3 → Code) :
    expressionValue (edgeExpression β J xs) =
      Real.log (edge (satInteraction (β : ℝ) J) (fun i => expressionValue (xs i))) := by
  rw [← exp_edgeExpression, Real.log_exp]

@[fun_prop] theorem spinsThree_computable :
    Computable (fun p : Bool × Bool × Bool => ![p.1,p.2.1,p.2.2]) := by
  apply computable_fin_lambda
  intro i
  fin_cases i <;> simp only [Matrix.cons_val_zero', Matrix.cons_val_succ']
  all_goals fun_prop

def extendSpins (a b ε : Bool) : Fin 3 → Bool := ![a,b,ε]

@[fun_prop] theorem extendSpins_computable :
    Computable (fun p : Bool × Bool × Bool => extendSpins p.1 p.2.1 p.2.2) :=
  spinsThree_computable

noncomputable def messageExpression (β : ℚ) (J : Fin 3 → Bool)
    (xs : Fin 2 → Code) (ε : Bool) : Code :=
  binaryLogSumExpression
    (binaryLogSumExpression
      (boltzmannAtom (clausePenalty β J (extendSpins false false ε)) xs ![false,false])
      (boltzmannAtom (clausePenalty β J (extendSpins false true ε)) xs ![false,true]))
    (binaryLogSumExpression
      (boltzmannAtom (clausePenalty β J (extendSpins true false ε)) xs ![true,false])
      (boltzmannAtom (clausePenalty β J (extendSpins true true ε)) xs ![true,true]))

@[fun_prop] theorem messageExpression_computable :
    Computable (fun p : ℚ × (Fin 3 → Bool) × (Fin 2 → Code) × Bool =>
      messageExpression p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  unfold messageExpression
  fun_prop

theorem appendSpin_three (a b ε : Bool) :
    appendSpin (p := 3) ![a,b] ε = ![a,b,ε] := by
  funext i
  fin_cases i <;> rfl

theorem messageExpression_value (β : ℚ) (J : Fin 3 → Bool)
    (xs : Fin 2 → Code) (ε : Bool) :
    expressionValue (messageExpression β J xs ε) =
      message (satInteraction (β : ℝ) J) (fun i => expressionValue (xs i)) ε := by
  rw [← Real.log_exp (expressionValue (messageExpression β J xs ε))]
  unfold messageExpression message
  congr 1
  simp only [exp_binaryLogSumExpression, exp_boltzmannAtom, clausePenalty_cast]
  simp_rw [sum_bool_vector_succ]
  simp only [Fintype.sum_unique]
  have ht (a b : Bool) (t : Fin 0 → Bool) : Fin.cons a (Fin.cons b t) = ![a,b] := by
    funext i
    fin_cases i <;> rfl
  simp only [ht, appendSpin_three, extendSpins]

abbrev SiteExpressionDatum := (Fin 3 → Bool) × (Fin 2 → Code)

noncomputable def siteExpression (β : ℚ) (data : List SiteExpressionDatum) : Code :=
  binaryLogMeanExpression
    (sumExpressions (data.map (fun z => messageExpression β z.1 z.2 false)))
    (sumExpressions (data.map (fun z => messageExpression β z.1 z.2 true)))

@[fun_prop] theorem siteExpression_computable :
    Computable (fun p : ℚ × List SiteExpressionDatum => siteExpression p.1 p.2) := by
  have hm (ε : Bool) : Computable (fun p : ℚ × List SiteExpressionDatum =>
      p.2.map (fun z => messageExpression p.1 z.1 z.2 ε)) := by
    apply computable_list_map Computable.snd
    unfold Computable₂
    fun_prop
  unfold siteExpression
  fun_prop

theorem siteExpression_value (β : ℚ) (data : List SiteExpressionDatum) :
    expressionValue (siteExpression β data) =
      siteLog (fun j : Fin data.length => satSample (β : ℝ) (data.get j).1) 0
        (fun i => expressionValue ((data.get i.1).2 i.2)) := by
  have hs (ε : Bool) : (data.map (fun z =>
      message (satInteraction (β : ℝ) z.1) (fun i => expressionValue (z.2 i)) ε)).sum =
      ∑ j : Fin data.length, message (satInteraction (β : ℝ) (data.get j).1)
        (fun i => expressionValue ((data.get j).2 i)) ε := by
    rw [← List.sum_ofFn]
    have h := congrArg (fun ds : List SiteExpressionDatum =>
      (ds.map (fun z => message (satInteraction (β : ℝ) z.1)
        (fun i => expressionValue (z.2 i)) ε)).sum) (List.ofFn_get data)
    simpa only [List.map_ofFn, Function.comp_def] using h.symm
  simp only [siteExpression, binaryLogMeanExpression_value, sumExpressions_value,
    List.map_map, Function.comp_def, messageExpression_value, hs]
  simp only [siteLog, zero_mul, zero_add, satSample, Fintype.sum_bool]
  congr 2
  exact add_comm _ _

attribute [local irreducible] edgeExpression siteExpression

theorem edgeExpression_comp {A : Type} [Primcodable A]
    (β : A → ℚ) (J : A → Fin 3 → Bool) (xs : A → Fin 3 → Code)
    (hβ : Computable β) (hJ : Computable J) (hx : Computable xs) :
    Computable (fun a => edgeExpression (β a) (J a) (xs a)) := by
  exact edgeExpression_computable.comp (hβ.pair (hJ.pair hx))

theorem siteExpression_comp {A : Type} [Primcodable A]
    (β : A → ℚ) (data : A → List SiteExpressionDatum)
    (hβ : Computable β) (hd : Computable data) :
    Computable (fun a => siteExpression (β a) (data a)) := by
  exact siteExpression_computable.comp (hβ.pair hd)

theorem siteExpression_ofFn_value {k : ℕ} (β : ℚ)
    (J : Fin k → Fin 3 → Bool) (xs : Fin k → Fin 2 → Code) :
    expressionValue (siteExpression β (List.ofFn (fun j => (J j,xs j)))) =
      siteLog (fun j => satSample (β : ℝ) (J j)) 0
        (fun i => expressionValue (xs i.1 i.2)) := by
  simp only [siteExpression, binaryLogMeanExpression_value, sumExpressions_value,
    List.map_ofFn, List.sum_ofFn, Function.comp_def, messageExpression_value]
  simp only [siteLog, zero_mul, zero_add, satSample, Fintype.sum_bool]
  congr 2
  exact add_comm _ _

end FixedClauseThreshold.Computability.FiniteArithmetic

end OAI
