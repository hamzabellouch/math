import Mathlib
import OAI.Combinatorics.IndependentSets.Reduction.Mixed
import OAI.Combinatorics.IndependentSets.Reduction.EnumerationSimple

namespace OAI

namespace LargeIndependentSets
open IndependentSetsGames.Foundations
open PCP Hastad.SourceContexts Hastad.SourceGame

namespace ExplicitEnum

def mapEquiv {A B : Type} (e : ExplicitEnum A) (f : A ≃ B) : ExplicitEnum B where
  values := e.values.map f
  nodup := e.nodup.map f.injective
  covers b := List.mem_map.mpr ⟨f.symm b,e.covers _,f.apply_symm_apply b⟩

def bool : ExplicitEnum Bool := ⟨[false,true],by decide,by intro b; cases b <;> simp⟩

def clauseAnswer : ExplicitEnum ClauseAnswer := mapEquiv (fin 8) clauseAnswerFinEquiv.symm

def slot : ExplicitEnum Slot := ⟨[.first,.second,.third],by decide,by intro s; cases s <;> simp⟩

def leftAnswer (u : ℕ) : ExplicitEnum (J u) := pi (fin u) (fun _ => clauseAnswer)
def rightAnswer (u : ℕ) : ExplicitEnum (I u) := pi (fin u) (fun _ => bool)
def clauses (F : Target.Formula) (u : ℕ) : ExplicitEnum (ClauseContext F u) :=
  pi (fin u) (fun _ => fin F.clauses.length)
def variablesEnum (F : Target.Formula) (u : ℕ) : ExplicitEnum (VariableContext F u) :=
  pi (fin u) (fun _ => fin F.variables)
def events (F : Target.Formula) (u : ℕ) : ExplicitEnum (Fin u → RandomEvent F) :=
  pi (fin u) (fun _ => prod (fin F.clauses.length) slot)

end ExplicitEnum

namespace NamedReduction
attribute [-instance] mixedTupleComputableFintype mixedTupleDecidableEq

noncomputable def staticCopies (p : SamplerParameters) (u : ℕ) :
    ExplicitEnum (p.Vertices (J u) (I u) Unit) := by
  classical
  exact ⟨Finset.univ.toList,Finset.nodup_toList _,fun x => Finset.mem_toList.mpr (Finset.mem_univ x)⟩

attribute [instance 1100] mixedTupleComputableFintype
attribute [instance] mixedTupleDecidableEq

instance cubeDecidableEq : (k : ℕ) → DecidableEq (BooleanJunta.Cube k)
  | 0 => inferInstanceAs (DecidableEq Unit)
  | k+1 => by
    letI := cubeDecidableEq k
    exact inferInstanceAs (DecidableEq (Bool × BooleanJunta.Cube k))

def vertexDecidable (p : SamplerParameters) (u : ℕ) (F : Target.Formula) :
    DecidableEq (p.Vertices (J u) (I u) (Fin u → RandomEvent F)) := by
  letI outcomeEq : DecidableEq (SamplerOutcome (J u) (I u) p.n p.s p.m p.k) := by
    unfold SamplerOutcome
    infer_instance
  delta SamplerParameters.Vertices RationalLaw.Vertices RationalLaw.Expanded
  exact @instDecidableEqProd _ _ (inferInstanceAs (DecidableEq (Fin p.n → Fin u → RandomEvent F)))
    (fun x y => decidable_of_iff (x.1=y.1 ∧ x.2.val=y.2.val) (by
      constructor
      · rintro ⟨h,hv⟩
        rcases x with ⟨a,i⟩
        rcases y with ⟨b,j⟩
        dsimp at h hv
        subst b
        have hi : i=j := Fin.ext hv
        subst j
        rfl
      · intro h; subst y; exact ⟨rfl,rfl⟩))

noncomputable def formula (H : RoundTables.BaseTable) (p : SamplerParameters)
    (u q : ℕ) (hq : 0<q) (F : Formula) : Graph := by
  let G := SemanticReduction.gapFormula H F
  letI := vertexDecidable p u G
  exact p.namedOutput q hq (LCInput.labelCover G u)
    (ExplicitEnum.clauses G u) (ExplicitEnum.variablesEnum G u)
    (ExplicitEnum.leftAnswer u) (ExplicitEnum.rightAnswer u)
    (ExplicitEnum.events G u) (staticCopies p u)

attribute [-instance] mixedTupleComputableFintype mixedTupleDecidableEq
noncomputable def formula_renaming (H : RoundTables.BaseTable) (p : SamplerParameters)
    (u q : ℕ) (hq : 0<q) (F : Formula) :
    Graph.Renaming (formula H p u q hq F) (SemanticReduction.reduce H p u q hq F) := by
  let G := SemanticReduction.gapFormula H F
  letI := vertexDecidable p u G
  exact p.namedOutput_renaming q hq (LCInput.labelCover G u)
    (ExplicitEnum.clauses G u) (ExplicitEnum.variablesEnum G u)
    (ExplicitEnum.leftAnswer u) (ExplicitEnum.rightAnswer u)
    (ExplicitEnum.events G u) (staticCopies p u)
attribute [instance 1100] mixedTupleComputableFintype
attribute [instance] mixedTupleDecidableEq

lemma bits_length_of_vertices (G H : Graph) (h : G.vertices=H.vertices) :
    (graphBits G).length = (graphBits H).length := by
  have hh (G : Graph) : (graphBits G).length = (nameBits G.vertices).length + G.vertices^2 := by
    unfold graphBits
    rw [List.length_append]
    congr 1
    have hx (xs : List (Fin G.vertices)) :
        (xs.flatMap (fun i => (List.finRange G.vertices).map (G.adj i))).length =
          xs.length * G.vertices := by
      induction xs with
      | nil => simp
      | cons i xs ih => simp only [List.flatMap_cons,List.length_append,List.length_map,
          List.length_finRange,List.length_cons,ih]; ring
    simpa only [List.length_finRange, pow_two] using hx (List.finRange G.vertices)
  rw [hh,hh,h]

noncomputable def total (H : RoundTables.BaseTable) (p : SamplerParameters)
    (u q : ℕ) (hq : 0<q) (b : List Bool) : Graph :=
  formula H p u q hq (BinaryParser.decode b)

theorem total_named_semantic_reduction {δ : ℚ} (hδ : 0<δ) :
    ∃ H : RoundTables.BaseTable, ∃ p : SamplerParameters, ∃ u q : ℕ, ∃ hq : 0<q,
    (∀ b, (graphBits (total H p u q hq b)).length ≤
      (SemanticReduction.totalPolynomial p u q).eval b.length) ∧
    (∀ F : Formula, F.Satisfiable → (total H p u q hq (formulaBits F)).ThreeColorable) ∧
    (∀ F : Formula, ¬F.Satisfiable →
      ((total H p u q hq (formulaBits F)).independenceNumber : ℚ) <
        δ*(total H p u q hq (formulaBits F)).vertices) := by
  obtain ⟨H,p,u,q,hq,hyes,hno⟩ := semantic_reduction hδ
  refine ⟨H,p,u,q,hq,?_,?_,?_⟩
  · intro b
    have e := formula_renaming H p u q hq (BinaryParser.decode b)
    have hl := bits_length_of_vertices _ _ e.vertices_eq
    change (graphBits (formula H p u q hq (BinaryParser.decode b))).length ≤ _
    rw [hl]
    exact SemanticReduction.total_output_bound H p u q hq b
  · intro F hF
    simpa only [total,BinaryParser.decode_encoded] using
      (formula_renaming H p u q hq F).symm.colorable (hyes F hF)
  · intro F hF
    have e := formula_renaming H p u q hq F
    have hv := e.vertices_eq
    have ha := e.alpha_eq
    simpa only [total,BinaryParser.decode_encoded,ha,hv] using hno F hF

end NamedReduction
end LargeIndependentSets

end OAI
