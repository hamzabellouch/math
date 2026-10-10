import OAI.Probability.SATComputability.HierarchySemantics

namespace OAI

namespace FixedClauseThreshold.Computability

open Encodable Denumerable Nat.Partrec FiniteArithmetic RapidForcing.EffectiveArithmetic
local instance hierarchyEvaluatorRatPrimcodable : Primcodable ℚ := PeriodicLattice.RecursiveArithmetic.ratPrimcodable

@[fun_prop] theorem codeAlphabet_computable : Computable codeAlphabet := by
  unfold codeAlphabet
  apply computable_list_map (by fun_prop)
  exact ((Primrec.ofNat Code).to_comp.comp Computable.snd).to₂

@[fun_prop] theorem hierarchyStates_computable :
    Computable (fun p : ℕ × ℕ => hierarchyStates p.1 p.2) := by
  unfold hierarchyStates
  exact words_primrec.to_comp.comp (codeAlphabet_computable.comp Computable.fst) Computable.snd

variable {A : Type}

attribute [local irreducible] hierarchyTable hierarchyStates chooseChildren
  tableLookup rationalExpression

noncomputable def trialExpression (leaf : A → List Code → Code) (a : A)
    (root : Code) (ms : List ℚ) (L : ℕ) : Code :=
  let states := hierarchyStates (encode root) L
  let tab := hierarchyTable states ms (states.map (fun ds => (ds, leaf a ds)))
  sumExpressions ((chooseChildren (List.replicate L root)).map (fun b =>
    Code.comp (rationalExpression b.1) (tableLookup tab b.2)))

theorem trialExpression_computable [Primcodable A] (leaf : A → List Code → Code)
    (hleaf : Computable (fun p : A × List Code => leaf p.1 p.2)) :
    Computable (fun p : A × Code × List ℚ × ℕ =>
      trialExpression leaf p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hc : Computable (fun p : Code × Code => p.1.comp p.2) :=
    Code.primrec₂_comp.to_comp
  have hr : Computable (fun p : ℕ × Code => List.replicate p.1 p.2) := by
    have h : Computable (fun p : ℕ × Code => (List.range p.1).map (fun _ => p.2)) := by
      apply computable_list_map (Primrec.list_range.to_comp.comp Computable.fst)
      unfold Computable₂
      fun_prop
    exact h.of_eq (fun p => by simp)
  have hi : Computable (fun p : A × Code × List ℚ × ℕ =>
      (hierarchyStates (encode p.2.1) p.2.2.2).map (fun ds => (ds, leaf p.1 ds))) := by
    apply computable_list_map (by fun_prop)
    unfold Computable₂
    fun_prop
  have ht : Computable (fun p : A × Code × List ℚ × ℕ =>
      hierarchyTable (hierarchyStates (encode p.2.1) p.2.2.2) p.2.2.1
        ((hierarchyStates (encode p.2.1) p.2.2.2).map (fun ds => (ds, leaf p.1 ds)))) := by
    fun_prop
  unfold trialExpression
  apply sumExpressions_computable.comp
  apply computable_list_map (by fun_prop)
  unfold Computable₂
  have hw : Computable (fun p : (A × Code × List ℚ × ℕ) × (ℚ × List Code) =>
      rationalExpression p.2.1) := rationalExpression_computable.comp (by fun_prop)
  have hl : Computable (fun p : (A × Code × List ℚ × ℕ) × (ℚ × List Code) =>
      tableLookup (hierarchyTable (hierarchyStates (encode p.1.2.1) p.1.2.2.2) p.1.2.2.1
        ((hierarchyStates (encode p.1.2.1) p.1.2.2.2).map (fun ds => (ds, leaf p.1.1 ds))))
          p.2.2) :=
    tableLookup_computable.comp ((ht.comp Computable.fst).pair (by fun_prop))
  exact hc.comp (hw.pair hl)

theorem trialExpression_value (leaf : A → List Code → Code) (a : A)
    (root : Code) (ms : List ℚ) (L : ℕ) :
    expressionValue (trialExpression leaf a root ms L) =
      branchSum (chooseChildren (List.replicate L root))
        (listLogMean ms (fun ds => expressionValue (leaf a ds))) := by
  have hroot : List.replicate L root ∈ hierarchyStates (encode root) L := by
    apply (mem_hierarchyStates _ _ _).mpr
    refine ⟨List.length_replicate, ?_⟩
    intro c hc
    have h := List.eq_of_mem_replicate hc
    subst c
    exact le_rfl
  simp only [trialExpression, sumExpressions_value, List.map_map,
    Function.comp_def, expressionValue, rationalExpression_value, branchSum]
  apply congrArg List.sum
  apply List.map_congr_left
  intro b hb
  congr 1
  apply hierarchyTable_value
  · intro cs hcs
    rw [tableLookup_map _ _ hcs]
  · exact chooseChildren_in_states hroot b hb

theorem trialExpression_eq_trialLog {L : ℕ} (leaf : A → List Code → Code) (a : A)
    (g : (Fin L → ℝ) → ℝ) (hleaf : ∀ ds, expressionValue (leaf a ds) = g (leafFields L ds))
    (root : Code) (ms : List ℚ) :
    expressionValue (trialExpression leaf a root ms L) =
      DilutedSpinGlass.trialLog ms.length
        (rationalTreeValue (ms.length+1) (decodeTree (ms.length+1) root))
        (fun i => (ms.get i : ℝ)) g := by
  rw [trialExpression_value]
  have hg : (fun ds => expressionValue (leaf a ds)) = fun ds => g (leafFields L ds) :=
    funext hleaf
  rw [hg, listTrialLog_eq_finite, finiteTrialLog_eq]

theorem trialExpression_effective [Primcodable A] (leaf : A → List Code → Code)
    (hleaf : Computable (fun p : A × List Code => leaf p.1 p.2)) :
    PeriodicLattice.CertifiedReal.Effective (fun p : A × Code × List ℚ × ℕ =>
      expressionValue (trialExpression leaf p.1 p.2.1 p.2.2.1 p.2.2.2)) :=
  expressionValue_effective.comp (trialExpression_computable leaf hleaf)

end FixedClauseThreshold.Computability

end OAI
