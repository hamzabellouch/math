import Mathlib
import OAI.Computability.VertexCover.Reduction.SimpleParallel
import OAI.Computability.VertexCover.Machines.InitialCorrect
import OAI.Computability.VertexCover.Machines.FiniteFunction

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                    
section

namespace VertexCover.Machine.SimpleLC
open UniqueGames.Foundations
open FormulaParser InitialTable ClauseProjection

abbrev Signature := (Fin 3 → Bool) × (Fin 3 × Fin 3 → Bool)
noncomputable def sigCode : Signature → List Bool :=
  prodBits (finiteCode (Fin 3 → Bool)) (finiteCode (Fin 3 × Fin 3 → Bool))
def signature (cs : ClauseData) : Signature :=
  (fun k => (lit cs k).1,fun kl => decide ((lit cs kl.1).2=(lit cs kl.2).2))
noncomputable def relation (s : Signature) (k : Fin 3) : FixedLC.Map 7 2 := fun label =>
  let P := patternEquiv.symm label
  let good := ∀ k l, s.2 (k,l)=true → flipSign (s.1 k) (P.val k)=flipSign (s.1 l) (P.val l)
  let norm := if good then P.val else fun j => flipSign (s.1 j) (if s.2 (j,0) then s.1 0 else false)
  finTwoEquiv.symm (flipSign (s.1 k) (norm k))

noncomputable def row (p : FormulaData × ℕ) : FixedLC.Row 7 2 :=
  let cs := p.1.2.getD (p.2/3) clauseDefault
  let k : Fin 3 := ⟨p.2%3,Nat.mod_lt _ (by decide)⟩
  ((p.2/3,(lit cs k).2),relation (signature cs) k)

noncomputable def signaturePoly : Poly unaryClauseCode sigCode signature := by
  let litAt (k : Fin 3) := ((Poly.identity unaryClauseCode).pair
    (Poly.const unaryClauseCode (finCode (n := 3)) k)).comp litPoly
  let signs := Poly.finiteFunction unaryClauseCode (fun cs k => (lit cs k).1)
    (fun k => ((litAt k).comp (Poly.fst boolBits natBits)).comp
      (Poly.finiteRecode boolBits boolBits_injective))
  let equalities := Poly.finiteFunction unaryClauseCode
    (fun cs (kl : Fin 3 × Fin 3) => decide ((lit cs kl.1).2=(lit cs kl.2).2))
    (fun kl => ((((litAt kl.1).comp (Poly.snd boolBits natBits)).pair
      ((litAt kl.2).comp (Poly.snd boolBits natBits))).comp Poly.natBEq).comp
        (Poly.finiteRecode boolBits boolBits_injective))
  exact signs.pair equalities

noncomputable def relationPoly : Poly (prodBits sigCode (finCode (n := 3)))
    (FixedLC.mapCode (a := 7) (b := 2)) (fun p => relation p.1 p.2) :=
  Poly.finite _ _ (prodBits_injective
    (prodBits_injective (finiteCode_injective _) (finiteCode_injective _)) (finCode_injective 3)) _
noncomputable def rowPoly : Poly (prodBits FormulaParser.dataCode natBits) FixedLC.rowCode row := by
  let enc := prodBits FormulaParser.dataCode natBits
  let F := Poly.fst FormulaParser.dataCode natBits
  let i := Poly.snd FormulaParser.dataCode natBits
  let j := (i.pair (Poly.const enc natBits 3)).comp Poly.natDiv
  let k := i.comp (Poly.finMod 3 (by decide))
  let rows := F.comp (Poly.snd natBits (listBits unaryClauseCode))
  let cs := (j.pair rows).comp (Poly.listGetD unaryClauseCode clauseDefault)
  exact ((j.pair (((cs.pair k).comp litPoly).comp (Poly.snd boolBits natBits))).pair
    (((cs.comp signaturePoly).pair k).comp relationPoly)).congr (fun p => by
      simp only [Function.comp_apply,row,List.headD_eq_head?_getD,List.head?_drop,
        List.getD_eq_getElem?_getD])

abbrev NEFormula := {F : Target.Formula // F.clauses ≠ []}
noncomputable def code (F : NEFormula) : List Bool := targetCode F.val
noncomputable def output (F : NEFormula) : FixedLC 7 2 where
  u := F.val.clauses.length
  v := F.val.variables
  M := F.val.clauses.length*3
  apos := by decide
  bpos := by decide
  Mpos := Nat.mul_pos (List.length_pos_iff.mpr F.property) (by decide)
  left := (simpleGame F.val F.property).left
  right := (simpleGame F.val F.property).right
  projection := (simpleGame F.val F.property).projection
 theorem output_toLC (F : NEFormula) : (output F).toLC=simpleGame F.val F.property := rfl

 theorem lit_clause (F : Target.Formula) (j : Fin F.clauses.length) (k : Fin 3) :
    lit (targetClauseData (PCP.clauseAt F j)) k =
      ((literalAt F j k).positive,(literalAt F j k).variableIndex.val) := by
  fin_cases k <;> rfl
 theorem signature_clause (F : Target.Formula) (j : Fin F.clauses.length) :
    signature (targetClauseData (PCP.clauseAt F j)) =
      (fun k => (literalAt F j k).positive,
       fun kl => decide ((literalAt F j kl.1).variableIndex=(literalAt F j kl.2).variableIndex)) := by
  apply Prod.ext
  · funext k; exact congrArg Prod.fst (lit_clause F j k)
  · funext kl
    simp only [signature,lit_clause,Fin.val_inj]
 theorem relation_clause (F : Target.Formula) (j : Fin F.clauses.length) (k : Fin 3) :
    relation (signature (targetClauseData (PCP.clauseAt F j))) k =
      fun label => finTwoEquiv.symm (flipSign (literalAt F j k).positive
        ((normalizePattern F j (patternEquiv.symm label)).val k)) := by
  rw [signature_clause]
  funext label
  by_cases hg : Consistent F j (patternEquiv.symm label)
  · rw [normalizePattern,ite_eq_left hg]
    simp only [relation,decide_eq_true_eq]
    unfold Consistent at hg
    rw [ite_eq_left hg]
  · rw [normalizePattern,ite_eq_right hg]
    simp only [relation,decide_eq_true_eq]
    unfold Consistent at hg
    rw [ite_eq_right hg]
    change finTwoEquiv.symm (flipSign _ (flipSign _ (if _ then _ else _))) = _
    congr 2

 theorem row_correct (F : NEFormula) (e : Fin (output F).M) :
    row (targetData F.val,e.val) =
      (((output F).left e |>.val,(output F).right e |>.val),(output F).projection e) := by
  let j := (finProdFinEquiv.symm e).1
  let k := (finProdFinEquiv.symm e).2
  have hd : e.val/3=j.val := rfl
  have hm : (⟨e.val%3,Nat.mod_lt _ (by decide)⟩ : Fin 3)=k := rfl
  dsimp only [row]
  rw [hd,hm,InitialTable.clause_lookup,lit_clause,relation_clause]
  apply Prod.ext
  · rfl
  · funext label
    simp only [output,simpleGame,game,normalizeLabel,Equiv.symm_apply_apply]
    rfl

noncomputable def outputPoly : Poly code FixedLC.code output := by
  let enc := FormulaParser.dataCode
  let u := (Poly.snd natBits (listBits unaryClauseCode)).comp
    (Poly.listLength unaryClauseCode clauseDefault)
  let v := Poly.fst natBits (listBits unaryClauseCode)
  let M := (u.pair (Poly.const enc natBits 3)).comp Poly.natMul
  let erase := fun F : NEFormula => targetData F.val
  let cu : Poly code natBits (fun F => (output F).u) :=
    u.encodeCongr erase (fun _ => rfl) (fun F => by simp [output,erase,targetData])
  let cv : Poly code natBits (fun F => (output F).v) :=
    v.encodeCongr erase (fun _ => rfl) (fun _ => rfl)
  let cm : Poly code natBits (fun F => (output F).M) :=
    M.encodeCongr erase (fun _ => rfl) (fun F => by simp [output,erase,targetData])
  let cr : Poly (prodBits code natBits) FixedLC.rowCode (fun p : NEFormula × ℕ => row (erase p.1,p.2)) :=
    rowPoly.encodeCongr (fun p : NEFormula × ℕ => (erase p.1,p.2)) (fun _ => rfl) (fun _ => rfl)
  let F₀ : NEFormula := ⟨⟨1,[#v[⟨0,true⟩,⟨0,true⟩,⟨0,true⟩]]⟩,by decide⟩
  exact FixedLC.materializePoly code F₀ output (by decide) cu cv cm cr row_correct
end VertexCover.Machine.SimpleLC
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
