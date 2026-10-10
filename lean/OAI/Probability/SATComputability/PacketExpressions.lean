import OAI.Probability.SATComputability.HierarchyEvaluator
import OAI.Probability.SATComputability.CavityExpressions
import OAI.Probability.DilutedSpin.FiniteEncoding

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass Nat.Partrec FiniteArithmetic RapidForcing.EffectiveArithmetic
local instance packetExpressionsRatPrimcodable : Primcodable ℚ := PeriodicLattice.RecursiveArithmetic.ratPrimcodable

noncomputable def fieldExpression (cs : List Code) (i : ℕ) : Code :=
  rationalExpression (decodedRational (cs[i]?.getD .zero))

@[fun_prop] theorem fieldExpression_computable :
    Computable (fun p : List Code × ℕ => fieldExpression p.1 p.2) := by
  have hget : Computable (fun p : List Code × ℕ => p.1[p.2]?.getD Code.zero) :=
    (Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.fst Primrec.snd)
      (Primrec.const Code.zero)).to_comp
  unfold fieldExpression
  fun_prop

theorem fieldExpression_value (cs : List Code) (i : ℕ) :
    expressionValue (fieldExpression cs i) = (decodedRational (cs[i]?.getD .zero) : ℝ) := by
  exact rationalExpression_value _

attribute [local irreducible] fieldExpression edgeExpression siteExpression trialExpression

noncomputable def fieldVector (k : ℕ) (cs : List Code) : Fin k → Code :=
  fun i => fieldExpression cs i.val

@[fun_prop] theorem fieldVector_computable (k : ℕ) : Computable (fieldVector k) := by
  apply computable_fin_lambda
  intro i
  exact fieldExpression_computable.comp (Computable.id.pair (Computable.const i.val))

attribute [local irreducible] fieldVector

noncomputable def edgeLeaf (p : ℚ × (Fin 3 → Bool)) (cs : List Code) : Code :=
  edgeExpression p.1 p.2 (fieldVector 3 cs)

attribute [local irreducible] edgeLeaf

@[fun_prop] theorem edgeLeaf_computable :
    Computable (fun p : (ℚ × (Fin 3 → Bool)) × List Code => edgeLeaf p.1 p.2) := by
  have hf := (fieldVector_computable 3).comp
    (show Computable (fun p : (ℚ × (Fin 3 → Bool)) × List Code => p.2) from Computable.snd)
  unfold edgeLeaf
  exact edgeExpression_comp _ _ _ (by fun_prop) (by fun_prop) hf

theorem edgeLeaf_value (p : ℚ × (Fin 3 → Bool)) (cs : List Code) :
    expressionValue (edgeLeaf p cs) =
      Real.log (edge (satInteraction (p.1 : ℝ) p.2) (leafFields 3 cs)) := by
  simp only [edgeLeaf, edgeExpression_value, fieldVector, fieldExpression_value]
  rfl

noncomputable def edgeTrialExpression (β : ℚ) (J : Fin 3 → Bool)
  (root : Code) (ms : List ℚ) : Code := trialExpression edgeLeaf (β,J) root ms 3

@[fun_prop] theorem edgeTrialExpression_computable :
    Computable (fun p : ℚ × (Fin 3 → Bool) × Code × List ℚ =>
      edgeTrialExpression p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have ht := trialExpression_computable edgeLeaf edgeLeaf_computable
  unfold edgeTrialExpression
  exact ht.comp (g := fun p : ℚ × (Fin 3 → Bool) × Code × List ℚ =>
    ((p.1,p.2.1),p.2.2.1,p.2.2.2,3)) (by fun_prop)

theorem edgeTrialExpression_value (β : ℚ) (J : Fin 3 → Bool)
    (root : Code) (ms : List ℚ) :
    expressionValue (edgeTrialExpression β J root ms) =
      trialLog ms.length (rationalTreeValue (ms.length+1) (decodeTree (ms.length+1) root))
        (fun i => (ms.get i : ℝ)) (fun x => Real.log (edge (satInteraction (β : ℝ) J) x)) := by
  exact trialExpression_eq_trialLog edgeLeaf (β,J) _ (fun cs => edgeLeaf_value _ cs) root ms

noncomputable def siteData (signs : List (Fin 3 → Bool)) (cs : List Code) :
    List SiteExpressionDatum :=
  (List.range signs.length).map (fun j =>
    (signs[j]?.getD (fun _ => false), fun i : Fin 2 => fieldExpression cs (2*j+i.val)))

attribute [local irreducible] siteData

@[fun_prop] theorem siteData_computable :
    Computable (fun p : List (Fin 3 → Bool) × List Code => siteData p.1 p.2) := by
  have hget : Computable (fun p : List (Fin 3 → Bool) × ℕ =>
      p.1[p.2]?.getD (fun _ => false)) :=
    (Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.fst Primrec.snd)
      (Primrec.const (fun _ : Fin 3 => false))).to_comp
  unfold siteData
  apply computable_list_map
    (f := fun p : List (Fin 3 → Bool) × List Code => List.range p.1.length)
    (g := fun p j => (p.1[j]?.getD (fun _ => false),
      fun i : Fin 2 => fieldExpression p.2 (2*j+i.val))) (by fun_prop)
  unfold Computable₂
  apply Computable.pair
  · exact hget.comp (g := fun p : (List (Fin 3 → Bool) × List Code) × ℕ =>
      (p.1.1,p.2)) ((Computable.fst.comp Computable.fst).pair Computable.snd)
  · apply computable_fin_lambda
    intro i
    exact fieldExpression_computable.comp
      (g := fun p : (List (Fin 3 → Bool) × List Code) × ℕ => (p.1.2,2*p.2+i.val))
      ((Computable.snd.comp Computable.fst).pair (by fun_prop))

theorem siteData_ofFn (signs : List (Fin 3 → Bool)) (cs : List Code) :
    siteData signs cs = List.ofFn (fun j : Fin signs.length =>
      (signs.get j, fun i : Fin 2 => fieldExpression cs (2*j.val+i.val))) := by
  apply List.ext_getElem
  · simp [siteData]
  · intro i hi hj
    have hi' : i < signs.length := by simpa only [List.length_ofFn] using hj
    simp [siteData, hi']

noncomputable def siteLeaf (p : ℚ × List (Fin 3 → Bool)) (cs : List Code) : Code :=
  siteExpression p.1 (siteData p.2 cs)

attribute [local irreducible] siteLeaf

@[fun_prop] theorem siteLeaf_computable :
    Computable (fun p : (ℚ × List (Fin 3 → Bool)) × List Code => siteLeaf p.1 p.2) := by
  have hd : Computable (fun p : (ℚ × List (Fin 3 → Bool)) × List Code =>
      siteData p.1.2 p.2) :=
    siteData_computable.comp
      (g := fun p : (ℚ × List (Fin 3 → Bool)) × List Code => (p.1.2,p.2))
      ((Computable.snd.comp Computable.fst).pair Computable.snd)
  have hb : Computable (fun p : (ℚ × List (Fin 3 → Bool)) × List Code => p.1.1) :=
    Computable.fst.comp Computable.fst
  unfold siteLeaf
  exact siteExpression_comp _ _ hb hd

theorem siteLeaf_value (p : ℚ × List (Fin 3 → Bool)) (cs : List Code) :
    expressionValue (siteLeaf p cs) =
      siteLog (fun j : Fin p.2.length => satSample (p.1 : ℝ) (p.2.get j)) 0
        (fun i => leafFields (p.2.length*2) cs (finProdFinEquiv i)) := by
  rw [siteLeaf, siteData_ofFn, siteExpression_ofFn_value]
  simp only [fieldExpression_value]
  have he : (fun i : Fin p.2.length × Fin 2 =>
      (decodedRational (cs[2*i.1.val+i.2.val]?.getD .zero) : ℝ)) =
      (fun i => leafFields (p.2.length*2) cs (finProdFinEquiv i)) := by
    funext i
    change (decodedRational (cs[2*i.1.val+i.2.val]?.getD .zero) : ℝ) =
      (decodedRational (cs[i.2.val+2*i.1.val]?.getD .zero) : ℝ)
    rw [Nat.add_comm (2*i.1.val)]
  rw [he]

noncomputable def siteTrialExpression (β : ℚ) (signs : List (Fin 3 → Bool))
    (root : Code) (ms : List ℚ) : Code :=
  trialExpression siteLeaf (β,signs) root ms (signs.length*2)

@[fun_prop] theorem siteTrialExpression_computable :
    Computable (fun p : ℚ × List (Fin 3 → Bool) × Code × List ℚ =>
      siteTrialExpression p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have ht := trialExpression_computable siteLeaf siteLeaf_computable
  unfold siteTrialExpression
  exact ht.comp (g := fun p : ℚ × List (Fin 3 → Bool) × Code × List ℚ =>
    ((p.1,p.2.1),p.2.2.1,p.2.2.2,p.2.1.length*2)) (by fun_prop)

theorem siteTrialExpression_value (β : ℚ) (signs : List (Fin 3 → Bool))
    (root : Code) (ms : List ℚ) :
    expressionValue (siteTrialExpression β signs root ms) =
      trialLog ms.length (rationalTreeValue (ms.length+1) (decodeTree (ms.length+1) root))
        (fun i => (ms.get i : ℝ))
          (siteLog (fun j : Fin signs.length => satSample (β : ℝ) (signs.get j)) 0) := by
  rw [siteTrialExpression, trialExpression_eq_trialLog siteLeaf (β,signs)
    (fun x => siteLog (fun j : Fin signs.length => satSample (β : ℝ) (signs.get j)) 0
      (fun i => x (finProdFinEquiv i)))
    (fun cs => siteLeaf_value (β,signs) cs)]
  exact trialLog_reindex finProdFinEquiv ms.length _ _ _

end FixedClauseThreshold.Computability

end OAI
