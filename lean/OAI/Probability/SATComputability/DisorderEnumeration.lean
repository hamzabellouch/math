import OAI.Probability.SATComputability.PacketExpressions
import OAI.Probability.SATComputability.PoissonEvaluation

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass Nat.Partrec FiniteArithmetic RapidForcing.EffectiveArithmetic
open scoped BigOperators Classical
local instance disorderEnumerationRatPrimcodable : Primcodable ℚ := PeriodicLattice.RecursiveArithmetic.ratPrimcodable

noncomputable def signAlphabet : List (Fin 3 → Bool) := Finset.univ.toList

@[fun_prop] theorem signWords_computable :
    Computable (fun k => words signAlphabet k) :=
  words_primrec.to_comp.comp (Computable.const signAlphabet) Computable.id

theorem sum_words {A : Type} [Fintype A] [DecidableEq A] (k : ℕ)
    (f : List A → ℝ) :
    ((words (Finset.univ.toList : List A) k).map f).sum =
      ∑ x : Fin k → A, f (List.ofFn x) := by
  induction k generalizing f with
  | zero => simp [words]
  | succ k ih =>
    simp only [words, List.map_flatMap, sum_flatMap_eq, List.map_map, Function.comp_def]
    simp_rw [ih]
    rw [Finset.sum_map_toList, ← (Fin.consEquiv (fun _ : Fin (k+1) => A)).sum_comp,
      Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro x _
    rw [List.ofFn_succ]
    rfl

noncomputable def averagedSiteExpression (β : ℚ) (root : Code) (ms : List ℚ) (k : ℕ) : Code :=
  .comp (rationalExpression ((8 : ℚ)^k)⁻¹)
    (sumExpressions ((words signAlphabet k).map (fun signs => siteTrialExpression β signs root ms)))

attribute [local irreducible] siteTrialExpression edgeTrialExpression

@[fun_prop] theorem averagedSiteExpression_computable :
    Computable (fun p : (ℚ × Code × List ℚ) × ℕ =>
      averagedSiteExpression p.1.1 p.1.2.1 p.1.2.2 p.2) := by
  have hs : Computable (fun p : (ℚ × Code × List ℚ) × ℕ =>
      (words signAlphabet p.2).map (fun signs =>
        siteTrialExpression p.1.1 signs p.1.2.1 p.1.2.2)) := by
    apply computable_list_map (signWords_computable.comp Computable.snd)
    unfold Computable₂
    exact siteTrialExpression_computable.comp
      (g := fun p : ((ℚ × Code × List ℚ) × ℕ) × List (Fin 3 → Bool) =>
        (p.1.1.1,p.2,p.1.1.2.1,p.1.1.2.2)) (by fun_prop)
  unfold averagedSiteExpression
  fun_prop

theorem trialLog_site_cast {k l r : ℕ} (h : k = l) (β : ℝ)
    (ζ : Hierarchy (r+1)) (m : Fin r → ℝ) (J : Fin l → Fin 3 → Bool) :
    trialLog r ζ m (siteLog (fun j : Fin k => satSample β (J (Fin.cast h j))) 0) =
      trialLog r ζ m (siteLog (fun j => satSample β (J j)) 0) := by
  subst l
  rfl

theorem averagedSiteExpression_value (β : ℚ) (root : Code) (ms : List ℚ) (k : ℕ) :
    expressionValue (averagedSiteExpression β root ms k) =
      (FiniteLaw.uniform : FiniteLaw (Fin k → Fin 3 → Bool)).expect (fun signs =>
        trialLog ms.length (rationalTreeValue (ms.length+1) (decodeTree (ms.length+1) root))
          (fun i => (ms.get i : ℝ)) (siteLog (fun j => satSample (β : ℝ) (signs j)) 0)) := by
  simp only [averagedSiteExpression, expressionValue, rationalExpression_value,
    sumExpressions_value, List.map_map, Function.comp_def, signAlphabet, sum_words]
  simp only [FiniteLaw.expect, FiniteLaw.uniform, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat, Rat.cast_inv, Rat.cast_pow,
    Rat.cast_ofNat, ← Finset.mul_sum]
  norm_num
  apply Finset.sum_congr rfl
  intro J _
  rw [siteTrialExpression_value]
  simpa only [List.get_ofFn, List.get_eq_getElem, List.getElem_ofFn, Fin.cast] using
    trialLog_site_cast (List.length_ofFn (f := J)) (β : ℝ)
      (rationalTreeValue (ms.length+1) (decodeTree (ms.length+1) root))
      (fun i => (ms.get i : ℝ)) J

noncomputable def averagedEdgeExpression (β : ℚ) (root : Code) (ms : List ℚ) : Code :=
  .comp (rationalExpression (1/8))
    (sumExpressions (signAlphabet.map (fun J => edgeTrialExpression β J root ms)))

@[fun_prop] theorem averagedEdgeExpression_computable :
    Computable (fun p : ℚ × Code × List ℚ => averagedEdgeExpression p.1 p.2.1 p.2.2) := by
  have hs : Computable (fun p : ℚ × Code × List ℚ =>
      signAlphabet.map (fun J => edgeTrialExpression p.1 J p.2.1 p.2.2)) := by
    apply computable_list_map (Computable.const signAlphabet)
    unfold Computable₂
    exact edgeTrialExpression_computable.comp
      (g := fun p : (ℚ × Code × List ℚ) × (Fin 3 → Bool) =>
        (p.1.1,p.2,p.1.2.1,p.1.2.2)) (by fun_prop)
  unfold averagedEdgeExpression
  fun_prop

theorem averagedEdgeExpression_value (β : ℚ) (root : Code) (ms : List ℚ) :
    expressionValue (averagedEdgeExpression β root ms) =
      (FiniteLaw.uniform : FiniteLaw (Fin 3 → Bool)).expect (fun J =>
        trialLog ms.length (rationalTreeValue (ms.length+1) (decodeTree (ms.length+1) root))
          (fun i => (ms.get i : ℝ)) (fun x => Real.log (edge (satInteraction (β : ℝ) J) x))) := by
  simp only [averagedEdgeExpression, expressionValue, rationalExpression_value,
    sumExpressions_value, List.map_map, Function.comp_def, signAlphabet, Finset.sum_map_toList,
    edgeTrialExpression_value]
  simp only [FiniteLaw.expect, FiniteLaw.uniform, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat, Rat.cast_div, Rat.cast_one,
    Rat.cast_ofNat, ← Finset.mul_sum]
  norm_num

end FixedClauseThreshold.Computability

end OAI
