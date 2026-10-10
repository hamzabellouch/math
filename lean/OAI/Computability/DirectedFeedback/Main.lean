import Mathlib
import OAI.Computability.DirectedFeedback.Machines.OutputSize
import OAI.Computability.DirectedFeedback.RankGraph.PacketLocality
import OAI.Computability.DirectedFeedback.CookLevin.NPTableau

namespace OAI

section

noncomputable section
open scoped Classical
namespace DirectedFeedback.CookLevin
open DFVSGames.Foundations.PCP DFVSGames.Foundations
namespace LocalCSP

variable {I E J : Type} [Fintype I] [Fintype E] [Fintype J] [Nonempty I]
  (C : LocalCSP Bool I E J)

abbrev queryCount := Fintype.card J + 3

def asVerifier : VerifierToCNF.FiniteVerifier (Fintype.card (J ⊕ Fin 3)) :=
  let D := (C.pad (Fin 3)).reindex (Fintype.equivFin I) (Fintype.equivFin E)
      (Fintype.equivFin (J ⊕ Fin 3))
  ⟨Fintype.card I,Fintype.card E,D.query,D.accepts⟩

def asFormula : Target.Formula := VerifierToCNF.convert C.asVerifier (by simp)

theorem convert_satisfiable_iff {q : ℕ} (V : VerifierToCNF.FiniteVerifier q) (hq : 3 ≤ q) :
    (VerifierToCNF.convert V hq).Satisfiable ↔
      ∃ A, ∀ e, VerifierToCNF.eventValue V A e = true := by
  constructor
  · rintro ⟨B,hB⟩
    refine ⟨VerifierToCNF.restrictAssignment V B,?_⟩
    have hzero : VerifierToCNF.clauseFailures (VerifierToCNF.convert V hq).clauses B = 0 := by
      simp only [VerifierToCNF.clauseFailures,List.count_eq_zero]
      intro hm
      obtain ⟨c,hc,he⟩ := List.mem_map.mp hm
      rw [hB c hc] at he
      contradiction
    intro e
    cases he : VerifierToCNF.eventValue V (VerifierToCNF.restrictAssignment V B) e with
    | true => rfl
    | false =>
      have hbad := VerifierToCNF.eventBlock_failed V hq B e he
      have hle := VerifierToCNF.clauseFailures_le_flatMap (List.finRange V.events)
        (VerifierToCNF.eventBlock V hq) B e (by simp)
      change _ ≤ VerifierToCNF.clauseFailures (VerifierToCNF.convert V hq).clauses B at hle
      omega
  · rintro ⟨A,hA⟩
    exact VerifierToCNF.convert_completeness V hq A hA

theorem asFormula_satisfiable_iff : C.asFormula.Satisfiable ↔ C.Satisfiable := by
  rw [asFormula, convert_satisfiable_iff]
  change ((C.pad (Fin 3)).reindex (Fintype.equivFin I) (Fintype.equivFin E)
      (Fintype.equivFin (J ⊕ Fin 3))).Satisfiable ↔ C.Satisfiable
  rw [reindex_satisfiable_iff,pad_satisfiable_iff]

end LocalCSP

namespace NPTableau
open Turing
attribute [local instance] FinTM2.ΛFin

def alphabetCodec (V : NPVerifier) : FiniteCodec (Atom V.computation.tm.Γ
    V.computation.tm.Λ V.computation.tm.σ) := by
  have := atom_finite V
  have := atom_nonempty V
  letI := Fintype.ofFinite (Atom V.computation.tm.Γ V.computation.tm.Λ V.computation.tm.σ)
  exact oneHotCodec _

instance codec_width_nonempty (V : NPVerifier) : Nonempty (Fin (alphabetCodec V).width) := by
  have := atom_finite V
  have := atom_nonempty V
  let := Fintype.ofFinite (Atom V.computation.tm.Γ V.computation.tm.Λ V.computation.tm.σ)
  change Nonempty (Fin (Fintype.card (Atom V.computation.tm.Γ V.computation.tm.Λ V.computation.tm.σ)))
  infer_instance

def formula (V : NPVerifier) (input : List Bool) : Target.Formula :=
  ((tests V input).booleanize (alphabetCodec V)).asFormula

theorem formula_satisfiable_iff (V : NPVerifier) (input : List Bool) :
    (formula V input).Satisfiable ↔ V.Accepts input := by
  rw [formula,LocalCSP.asFormula_satisfiable_iff,LocalCSP.booleanize_satisfiable_iff,
    tests_satisfiable_iff]

end NPTableau
end DirectedFeedback.CookLevin

end
end

section

noncomputable section
open scoped Classical
namespace DirectedFeedback.CookLevin

def LocalCSP.padAt {A I E J : Type} (C : LocalCSP A I E J) (P : Type) (default : I) :
    LocalCSP A I E (J ⊕ P) :=
  ⟨fun e => Sum.elim (C.query e) (fun _ => default),
    fun e pattern => C.accepts e (pattern ∘ Sum.inl)⟩

theorem LocalCSP.padAt_satisfiable_iff {A I E J : Type} (C : LocalCSP A I E J) (P : Type) (d : I) :
    (C.padAt P d).Satisfiable ↔ C.Satisfiable := Iff.rfl

namespace NPTableau
open Turing DFVSGames.Foundations DFVSGames.Foundations.PCP
attribute [local instance] FinTM2.ΛFin

def eventCount (H S : Nat) := (S+1)+H*(S+1)+1

def decodeEvent (H S : Nat) (e : Fin (eventCount H S)) : TableauEvent H S :=
  if h : e.val < S+1 then .inl ⟨e.val,h⟩
  else if h' : e.val-(S+1) < H*(S+1) then
    .inr (.inl (finProdFinEquiv.symm ⟨e.val-(S+1),h'⟩))
  else .inr (.inr ())

theorem decodeEvent_surjective (H S : Nat) : Function.Surjective (decodeEvent H S) := by
  intro e
  rcases e with j | (tj | u)
  · refine ⟨⟨j.val,by dsimp [eventCount]; omega⟩,?_⟩
    simp [decodeEvent,j.isLt]
  · let i := finProdFinEquiv tj
    refine ⟨⟨S+1+i.val,by have := i.isLt; dsimp [eventCount]; omega⟩,?_⟩
    simp only [decodeEvent,show ¬ S+1+i.val<S+1 by omega,Nat.add_sub_cancel_left,
      dite_eq_left i.isLt]
    exact congrArg (fun t => Sum.inr (Sum.inl t)) (finProdFinEquiv.symm_apply_apply tj)
  · cases u
    refine ⟨⟨S+1+H*(S+1),by dsimp [eventCount]; omega⟩,?_⟩
    simp [decodeEvent,show ¬ S+1+H*(S+1)<S+1 by omega]

abbrev FixedSlot (V : NPVerifier) :=
  (TableauSlot V.computation.tm × Fin (alphabetCodec V).width) ⊕ Fin 3

def queryNumber (V : NPVerifier) : Nat := Fintype.card (FixedSlot V)

def slotIndex (V : NPVerifier) : FixedSlot V ≃ Fin (queryNumber V) := Fintype.equivFin _

def variableIndex (H S w : Nat) : ((TracePosition H S) × Fin w) ≃ Fin ((H+1)*(S+1)*w) :=
  (Equiv.prodCongr finProdFinEquiv (Equiv.refl _)).trans finProdFinEquiv

theorem variableIndex_val (H S w : Nat) (p : TracePosition H S) (b : Fin w) :
    (variableIndex H S w (p,b)).val = (p.1.val*(S+1)+p.2.val)*w+b.val := by
  simp [variableIndex,finProdFinEquiv,Nat.mul_comm,Nat.add_comm]

def canonicalVerifier (V : NPVerifier) (input : List Bool) :
    VerifierToCNF.FiniteVerifier (queryNumber V) :=
  let H := horizon V input.length
  let S := capacity V input.length
  let C := ((tests V input).booleanize (alphabetCodec V)).padAt (Fin 3) ((0,0),Classical.choice (codec_width_nonempty V))
  { «variables» := (H+1)*(S+1)*(alphabetCodec V).width
    events := eventCount H S
    query := fun e i => variableIndex H S _ (C.query (decodeEvent H S e) ((slotIndex V).symm i))
    accepts := fun e p => C.accepts (decodeEvent H S e) (p ∘ slotIndex V) }

theorem canonicalVerifier_satisfiable_iff (V : NPVerifier) (input : List Bool) :
    (∃ A, ∀ e, VerifierToCNF.eventValue (canonicalVerifier V input) A e = true) ↔ V.Accepts input := by
  let H := horizon V input.length
  let S := capacity V input.length
  let C := ((tests V input).booleanize (alphabetCodec V)).padAt (Fin 3) ((0,0),Classical.choice (codec_width_nonempty V))
  have he : (∃ A, ∀ e, VerifierToCNF.eventValue (canonicalVerifier V input) A e = true) ↔
      C.Satisfiable := by
    constructor
    · rintro ⟨A,hA⟩
      refine ⟨A ∘ variableIndex H S _,?_⟩
      intro e
      obtain ⟨i,hi⟩ := decodeEvent_surjective H S e
      have hh := hA i
      simp only [canonicalVerifier,VerifierToCNF.eventValue,Function.comp_def,
        Equiv.symm_apply_apply] at hh
      change C.accepts (decodeEvent H S i)
        (fun s => A (variableIndex H S _ (C.query (decodeEvent H S i) s))) = true at hh
      rw [hi] at hh
      exact hh
    · rintro ⟨A,hA⟩
      refine ⟨A ∘ (variableIndex H S _).symm,?_⟩
      intro e
      simp only [canonicalVerifier,VerifierToCNF.eventValue,Function.comp_def,
        Equiv.symm_apply_apply]
      change C.accepts (decodeEvent H S e) (fun s => A ((variableIndex H S _).symm
        (variableIndex H S _ (C.query (decodeEvent H S e) s)))) = true
      have hp : (fun s => A ((variableIndex H S _).symm
          (variableIndex H S _ (C.query (decodeEvent H S e) s)))) =
          A ∘ C.query (decodeEvent H S e) := by
        funext s
        exact congrArg A ((variableIndex H S _).symm_apply_apply _)
      rw [hp]
      exact hA (decodeEvent H S e)
  rw [he]
  change (((tests V input).booleanize (alphabetCodec V)).padAt (Fin 3) ((0,0),Classical.choice (codec_width_nonempty V))).Satisfiable ↔ _
  rw [LocalCSP.padAt_satisfiable_iff,LocalCSP.booleanize_satisfiable_iff,tests_satisfiable_iff]

theorem queryNumber_ge (V : NPVerifier) : 3 ≤ queryNumber V := by
  simp [queryNumber,FixedSlot]

def canonicalFormula (V : NPVerifier) (input : List Bool) : Target.Formula :=
  VerifierToCNF.convert (canonicalVerifier V input) (queryNumber_ge V)

theorem canonicalFormula_correct (V : NPVerifier) (input : List Bool) :
    (canonicalFormula V input).Satisfiable ↔ V.Accepts input := by
  rw [canonicalFormula,LocalCSP.convert_satisfiable_iff,canonicalVerifier_satisfiable_iff]

end NPTableau
end DirectedFeedback.CookLevin

end
end

section

noncomputable section
open scoped Classical
namespace DirectedFeedback.CookLevin
open Turing BoundedExpr
variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
  [Fintype σ] [Fintype Λ] [∀ k, Fintype (Γ k)] {r : Nat}

def WDef (S : List Bool → (Fin r → Nat) → Words Γ) : Prop :=
  ∀ k (i : List Bool → (Fin r → Nat) → Nat), Def i → FDef (fun x a => S x a k (i x a))

namespace WDef
variable {S T : List Bool → (Fin r → Nat) → Words Γ}

omit [DecidableEq K] [∀ k, Fintype (Γ k)] in
theorem congr (hS : WDef S) (h : ∀ x a k i, S x a k i = T x a k i) : WDef T :=
  fun k i hi => (hS k i hi).congr (fun x a => h x a k (i x a))

omit [DecidableEq K] [∀ k, Fintype (Γ k)] in
theorem ite {p : List Bool → (Fin r → Nat) → Prop} (hp : PDef p)
    (hS : WDef S) (hT : WDef T) : WDef (fun x a => if p x a then S x a else T x a) := by
  intro k i hi
  exact (hp.ite (hS k i hi) (hT k i hi)).congr (by intro x a; split <;> simp_all)

omit [∀ k, Fintype (Γ k)] in
theorem update (hS : WDef S) (k : K)
    {f : List Bool → (Fin r → Nat) → Nat → Option (Γ k)}
    (hf : ∀ i, Def i → FDef (fun x a => f x a (i x a))) :
    WDef (fun x a => Function.update (S x a) k (f x a)) := by
  intro j i hi
  by_cases h : j=k
  · subst j
    simpa using hf i hi
  · simpa only [Function.update_of_ne h] using hS j i hi

theorem push (hS : WDef S) (k : K) {v : List Bool → (Fin r → Nat) → Γ k} (hv : FDef v) :
    WDef (fun x a => Function.update (S x a) k (wordPush (v x a) (S x a k))) := by
  apply hS.update k
  intro i hi
  have hh := (PDef.nat_eq hi (Def.lit 0)).ite (hv.map some) (hS k _ (hi.sub (Def.lit 1)))
  apply hh.congr
  intro x a
  cases i x a <;> simp [wordPush]

omit [∀ k, Fintype (Γ k)] in
theorem pop (hS : WDef S) (k : K) :
    WDef (fun x a => Function.update (S x a) k (wordPop (S x a k))) :=
  hS.update k (fun _i hi => hS k _ (hi.add (Def.lit 1)))
end WDef

structure CDef (c : List Bool → (Fin r → Nat) → WordCfg Γ Λ σ) : Prop where
  label : FDef (fun x a => (c x a).label)
  var : FDef (fun x a => (c x a).var)
  stk : WDef (fun x a => (c x a).stk)

namespace CDef
variable {c d : List Bool → (Fin r → Nat) → WordCfg Γ Λ σ}

omit [DecidableEq K] [Fintype σ] [Fintype Λ] [∀ k, Fintype (Γ k)] in
theorem congr (hc : CDef c) (h : ∀ x a, c x a=d x a) : CDef d := by
  have he : c=d := funext (fun x => funext (h x))
  rwa [← he]

omit [DecidableEq K] [Fintype σ] [Fintype Λ] [∀ k, Fintype (Γ k)] in
theorem ite {p : List Bool → (Fin r → Nat) → Prop} (hp : PDef p)
    (hc : CDef c) (hd : CDef d) : CDef (fun x a => if p x a then c x a else d x a) := by
  constructor
  · exact (hp.ite hc.label hd.label).congr (by intro x a; split <;> simp_all)
  · exact (hp.ite hc.var hd.var).congr (by intro x a; split <;> simp_all)
  · exact (WDef.ite hp hc.stk hd.stk).congr (by intro x a k i; split <;> simp_all)

omit [DecidableEq K] [Fintype σ] [Fintype Λ] [∀ k, Fintype (Γ k)] in
theorem bind {A : Type} [Fintype A] {f : List Bool → (Fin r → Nat) → A}
    (hf : FDef f) {g : A → List Bool → (Fin r → Nat) → WordCfg Γ Λ σ}
    (hg : ∀ v, CDef (g v)) : CDef (fun x a => g (f x a) x a) := by
  constructor
  · exact hf.bind (fun v => (hg v).label)
  · exact hf.bind (fun v => (hg v).var)
  · intro k i hi
    exact hf.bind (fun v => (hg v).stk k i hi)
end CDef

omit [Fintype Λ] in
theorem wordStepAux_def (q : TM2.Stmt Γ Λ σ)
    {v : List Bool → (Fin r → Nat) → σ} {S : List Bool → (Fin r → Nat) → Words Γ}
    (hv : FDef v) (hS : WDef S) : CDef (fun x a => wordStepAux q (v x a) (S x a)) := by
  induction q generalizing v S with
  | push k f q ih => exact ih (hv) (hS.push k (hv.map f))
  | peek k f q ih => exact ih ((hv.pair (hS k _ (Def.lit 0))).map (fun z => f z.1 z.2)) hS
  | pop k f q ih => exact ih ((hv.pair (hS k _ (Def.lit 0))).map (fun z => f z.1 z.2)) (hS.pop k)
  | load f q ih => exact ih (hv.map f) hS
  | branch f q t ihq iht =>
    apply (CDef.ite (hv.map f |>.bool_true) (ihq hv hS) (iht hv hS)).congr
    intro x a
    dsimp [wordStepAux]
    cases f (v x a) <;> simp
  | goto f => exact ⟨hv.map (fun v => some (f v)),hv,hS⟩
  | halt => exact ⟨FDef.const none,hv,hS⟩

theorem wordNext_def (M : Λ → TM2.Stmt Γ Λ σ)
    {c : List Bool → (Fin r → Nat) → WordCfg Γ Λ σ} (hc : CDef c) :
    CDef (fun x a => wordNext M (c x a)) := by
  have hh := CDef.bind hc.label (g := fun l x a => match l with
    | none => c x a
    | some l => wordStepAux (M l) (c x a).var (c x a).stk) (by
      intro l
      cases l with
      | none => exact hc
      | some l => exact wordStepAux_def (M l) hc.var hc.stk)
  exact hh

end DirectedFeedback.CookLevin

end
end

section

noncomputable section
open scoped Classical
namespace DirectedFeedback.CookLevin
open BoundedExpr Turing
variable {K : Type} [DecidableEq K] [Fintype K] {Γ : K → Type} {Λ σ : Type}
  [Fintype σ] [Fintype Λ] [∀ k, Fintype (Γ k)] {r R : Nat}

omit [DecidableEq K] [Fintype K] in
theorem localWord_def {d : List Bool → (Fin r → Nat) → LocalData Γ Λ σ R}
    (hc : FDef (fun x a => (d x a).ctrl))
    (hh : ∀ i k, FDef (fun x a => (d x a).head i k))
    (hb : ∀ i k, FDef (fun x a => (d x a).band i k))
    {j : List Bool → (Fin r → Nat) → Nat} (hj : Def j) :
    CDef (fun x a => (d x a).wordCfg (j x a)) := by
  constructor
  · exact hc.map Prod.fst
  · exact hc.map Prod.snd
  · intro k i hi
    have head := FDef.select (fun t => hh t k) hi none
    have band := FDef.select (fun t => hb t k) (hi.sub (hj.sub (Def.lit R))) none
    have cond := (PDef.le (hj.sub (Def.lit R)) hi).and
      (PDef.lt hi ((hj.sub (Def.lit R)).add (Def.lit (2*R+1))))
    have result := (PDef.lt hi (Def.lit R)).ite head (cond.ite band (FDef.const none))
    apply result.congr
    intro x a
    dsimp [LocalData.wordCfg]
    by_cases h : i x a<R
    · simp [h]
    · by_cases hb : j x a-R ≤ i x a ∧ i x a<j x a-R+(2*R+1)
      · have hu : i x a-(j x a-R)<2*R+1 := by omega
        simp [h,hb,hu]
      · have hn : ¬(j x a ≤ i x a+R ∧ i x a<j x a-R+(2*R+1)) := by omega
        simp [h,hn]

def rawData (S j : Nat) (a : StepSlot R → Atom Γ Λ σ) : LocalData Γ Λ σ R where
  ctrl := (a (.inr (.inr 0))).1
  head := fun i k => if i.val<S then (a (.inl i)).2 k else none
  band := fun i k => if j-R+i.val<S then (a (.inr (.inl i))).2 k else none

def rawStepAccepts (M : Λ → TM2.Stmt Γ Λ σ) (S j : Nat)
    (a : StepSlot (programRadius M) → Atom Γ Λ σ) : Bool :=
  let w := wordNext M ((rawData S j a).wordCfg j)
  decide ((a (.inr (.inr 1))).1=(w.label,w.var) ∧
    (j<S → ∀ k, (a (.inr (.inr 2))).2 k=w.stk k j))

omit [Fintype σ] [∀ k, Fintype (Γ k)] in
theorem rawStepAccepts_eq (M : Λ → TM2.Stmt Γ Λ σ) {S : Nat} (j : Fin (S+1))
    (a : StepSlot (programRadius M) → Atom Γ Λ σ) :
    rawStepAccepts M S j.val a = stepAccepts M j a := by
  have hd : rawData S j.val a = dataOfQueries j a := by
    apply LocalData.ext
    · rfl
    · funext i k; simp only [rawData,dataOfQueries]
    · funext i k; simp only [rawData,dataOfQueries]
  simp only [rawStepAccepts,stepAccepts,hd,decide_eq_decide]

theorem rawStepAccepts_def (M : Λ → TM2.Stmt Γ Λ σ)
    {S j : List Bool → (Fin r → Nat) → Nat} (hS : Def S) (hj : Def j)
    (a : StepSlot (programRadius M) → Atom Γ Λ σ) :
    FDef (fun x v => rawStepAccepts M (S x v) (j x v) a) := by
  have hdata : CDef (fun x v => (rawData (S x v) (j x v) a).wordCfg (j x v)) := by
    apply localWord_def (d:=fun x v => rawData (S x v) (j x v) a)
      (FDef.const ((a (.inr (.inr 0))).1))
    · intro i k
      apply ((PDef.lt (Def.lit i.val) hS).ite (FDef.const ((a (.inl i)).2 k)) (FDef.const none)).congr
      intro x v
      dsimp [rawData]
      split_ifs <;> rfl
    · intro i k
      apply ((PDef.lt ((hj.sub (Def.lit (programRadius M))).add (Def.lit i.val)) hS).ite
        (FDef.const ((a (.inr (.inl i))).2 k)) (FDef.const none)).congr
      intro x v
      dsimp [rawData]
      split_ifs <;> rfl
    · exact hj
  have hw := wordNext_def M hdata
  have hp := (PDef.eq (FDef.const ((a (.inr (.inr 1))).1)) (hw.label.pair hw.var)).and
    ((PDef.lt hj hS).imp (PDef.all (fun k => PDef.eq (FDef.const ((a (.inr (.inr 2))).2 k)) (hw.stk k j hj))))
  apply hp.decide.congr
  intro x v
  simp only [rawStepAccepts,decide_eq_decide]

namespace NPTableau
attribute [local instance] FinTM2.ΛFin FinTM2.kFin FinTM2.σFin

noncomputable instance verifierAlphabet (V : NPVerifier) (k : V.computation.tm.K) :
    Fintype (V.computation.tm.Γ k) := @Fintype.ofFinite _ (V.finiteAlphabet k)

theorem certBound_def (V : NPVerifier) {r : Nat} : Def (fun (x : List Bool) (_ : Fin r → Nat) => certBound V x.length) :=
  Def.length.poly V.witnessBound

theorem inputBound_def (V : NPVerifier) {r : Nat} : Def (fun (x : List Bool) (_ : Fin r → Nat) => inputBound V x.length) :=
  (((Def.lit 2).mul Def.length).add (certBound_def V)).add (Def.lit 1)

theorem horizon_def (V : NPVerifier) {r : Nat} : Def (fun (x : List Bool) (_ : Fin r → Nat) => horizon V x.length) :=
  (inputBound_def V).poly V.computation.time

theorem capacity_def (V : NPVerifier) {r : Nat} : Def (fun (x : List Bool) (_ : Fin r → Nat) => capacity V x.length) :=
  (inputBound_def V).add ((horizon_def V).mul (Def.lit _))

theorem fixedPrefix_def (V : NPVerifier) {r : Nat} :
    LDef (fun x (_ : Fin r → Nat) => fixedPrefix V x) :=
  ((((LDef.replicate Def.length true).append (LDef.const [false])).append LDef.input).map
    V.computation.inputAlphabet.invFun)

def rawInitialAccepts (V : NPVerifier) (x : List Bool) (j : Nat)
    (a : Fin 3 → Atom V.computation.tm.Γ V.computation.tm.Λ V.computation.tm.σ) : Bool :=
  decide (initialPredicate V.computation.tm (fixedPrefix V x) (certBound V x.length) j (a 0).1
    (fun k => if j<capacity V x.length then (a 1).2 k else none)
    (fun k => if j+1<capacity V x.length then (a 2).2 k else none))

theorem rawInitialAccepts_eq (V : NPVerifier) (x : List Bool) (j : Fin (capacity V x.length+1))
    (a : Fin 3 → Atom V.computation.tm.Γ V.computation.tm.Λ V.computation.tm.σ) :
    rawInitialAccepts V x j.val a =
      initialAccepts V.computation.tm (fixedPrefix V x) (certBound V x.length) j a := by
  simp only [rawInitialAccepts,initialAccepts]

theorem rawInitialAccepts_def (V : NPVerifier) {r : Nat}
    {j : List Bool → (Fin r → Nat) → Nat} (hj : Def j)
    (a : Fin 3 → Atom V.computation.tm.Γ V.computation.tm.Λ V.computation.tm.σ) :
    FDef (fun x v => rawInitialAccepts V x (j x v) a) := by
  let tm := V.computation.tm
  have cur (k : tm.K) := (PDef.lt hj (capacity_def V)).ite
    (FDef.const ((a 1).2 k)) (FDef.const none)
  have next (k : tm.K) := (PDef.lt (hj.add (Def.lit 1)) (capacity_def V)).ite
    (FDef.const ((a 2).2 k)) (FDef.const none)
  have hp := fixedPrefix_def (r:=r) V
  have hctrl : PDef (r:=r) (fun (_ : List Bool) _ =>
      (a 0).1 = (some tm.main,tm.initialState)) := PDef.const _
  have hp' := hctrl.and ((PDef.all (fun k : tm.K => (PDef.const (k≠tm.k₀)).imp
    (PDef.eq (cur k) (FDef.const none)))).and
    (((PDef.lt hj hp.length).imp (PDef.eq (cur tm.k₀) (hp.get j hj))).and
    (((PDef.le (hp.length.add (certBound_def V)) hj).imp (PDef.eq (cur tm.k₀) (FDef.const none))).and
    ((PDef.le hp.length hj).imp ((PDef.eq (cur tm.k₀) (FDef.const none)).imp
      (PDef.eq (next tm.k₀) (FDef.const none)))))))
  apply hp'.decide.congr
  intro x v
  by_cases h : j x v < capacity V x.length <;>
    by_cases h' : j x v+1 < capacity V x.length <;>
      simp [rawInitialAccepts,initialPredicate,h,h',tm]

end NPTableau
end DirectedFeedback.CookLevin

end
end

section

noncomputable section
open scoped Classical
namespace DirectedFeedback.CookLevin
open BoundedExpr Turing
attribute [local instance] FinTM2.ΛFin

def rawCell (S i : Nat) : Nat := if i < S then i+1 else 0

theorem rawCell_eq (S i : Nat) : rawCell S i = (cellAddress S i).val := by
  dsimp [rawCell,cellAddress]
  split_ifs <;> rfl

theorem rawCell_def {r : Nat} {S i : List Bool → (Fin r → Nat) → Nat}
    (hS : Def S) (hi : Def i) : Def (fun x a => rawCell (S x a) (i x a)) := by
  apply ((PDef.lt hi hS).nite (hi.add (Def.lit 1)) (Def.lit 0)).congr
  intro x a
  simp only [rawCell]
  split_ifs <;> rfl

def rawInitialQuery (S j : Nat) (i : Fin 3) : Nat × Nat :=
  if i.val=0 then (0,0) else if i.val=1 then (0,rawCell S j) else (0,rawCell S (j+1))

def rawStepQuery {R : Nat} (S t j : Nat) : StepSlot R → Nat × Nat
  | .inl i => (t,rawCell S i.val)
  | .inr (.inl i) => (t,rawCell S (j-R+i.val))
  | .inr (.inr i) => if i.val=0 then (t,0) else if i.val=1 then (t+1,0) else (t+1,rawCell S j)

theorem rawInitialQuery_eq {H S : Nat} (j : Fin (S+1)) (i : Fin 3) :
    rawInitialQuery S j.val i = ((initialQuery (H:=H) j i).1.val,(initialQuery (H:=H) j i).2.val) := by
  dsimp [rawInitialQuery,initialQuery]
  split_ifs <;> simp [rawCell_eq]

theorem rawStepQuery_eq {H S R : Nat} (t : Fin H) (j : Fin (S+1)) (i : StepSlot R) :
    rawStepQuery S t.val j.val i = ((stepQuery t j i).1.val,(stepQuery t j i).2.val) := by
  rcases i with i | (i | i)
  · simp [rawStepQuery,stepQuery,rawCell_eq]
  · simp [rawStepQuery,stepQuery,rawCell_eq]
  · dsimp [rawStepQuery,stepQuery]; split_ifs <;> simp [rawCell_eq]

def AddrDef {r : Nat} (f : List Bool → (Fin r → Nat) → Nat × Nat) : Prop :=
  Def (fun x a => (f x a).1) ∧ Def (fun x a => (f x a).2)

namespace AddrDef
variable {r : Nat} {f g : List Bool → (Fin r → Nat) → Nat × Nat}
theorem const (p : Nat × Nat) : AddrDef (r:=r) (fun _ _ => p) := ⟨Def.lit _,Def.lit _⟩
theorem ite {p : List Bool → (Fin r → Nat) → Prop} (hp : PDef p)
    (hf : AddrDef f) (hg : AddrDef g) : AddrDef (fun x a => if p x a then f x a else g x a) := by
  constructor
  · exact (hp.nite hf.1 hg.1).congr (by intro x a; by_cases h : p x a <;> simp [h])
  · exact (hp.nite hf.2 hg.2).congr (by intro x a; by_cases h : p x a <;> simp [h])
theorem congr (hf : AddrDef f) (h : ∀ x a, f x a=g x a) : AddrDef g :=
  ⟨hf.1.congr (fun x a => congrArg Prod.fst (h x a)),
    hf.2.congr (fun x a => congrArg Prod.snd (h x a))⟩
end AddrDef

theorem rawInitialQuery_def {r : Nat} {S j : List Bool → (Fin r → Nat) → Nat}
    (hS : Def S) (hj : Def j) (i : Fin 3) : AddrDef (fun x a => rawInitialQuery (S x a) (j x a) i) := by
  unfold rawInitialQuery
  split
  · exact AddrDef.const _
  · split
    · exact ⟨Def.lit 0,rawCell_def hS hj⟩
    · exact ⟨Def.lit 0,rawCell_def hS (hj.add (Def.lit 1))⟩

theorem rawStepQuery_def {r R : Nat} {S t j : List Bool → (Fin r → Nat) → Nat}
    (hS : Def S) (ht : Def t) (hj : Def j) (i : StepSlot R) :
    AddrDef (fun x a => rawStepQuery (S x a) (t x a) (j x a) i) := by
  rcases i with i | (i | i)
  · exact ⟨ht,rawCell_def hS (Def.lit _)⟩
  · exact ⟨ht,rawCell_def hS ((hj.sub (Def.lit R)).add (Def.lit i.val))⟩
  · dsimp only [rawStepQuery]
    split
    · exact ⟨ht,Def.lit 0⟩
    · split
      · exact ⟨ht.add (Def.lit 1),Def.lit 0⟩
      · exact ⟨ht.add (Def.lit 1),rawCell_def hS hj⟩

namespace NPTableau

def rawTableauQuery (tm : FinTM2) (H S e : Nat) (s : TableauSlot tm) : Nat × Nat :=
  if e < S+1 then match s with
    | .inl i => rawInitialQuery S e i
    | _ => (0,0)
  else if e-(S+1) < H*(S+1) then match s with
    | .inr (.inl i) => rawStepQuery S ((e-(S+1))/(S+1)) ((e-(S+1))%(S+1)) i
    | _ => (0,0)
  else match s with
    | .inr (.inr _) => (H,rawCell S 0)
    | _ => (0,0)

theorem rawTableauQuery_def (tm : FinTM2) {r : Nat}
    {H S e : List Bool → (Fin r → Nat) → Nat} (hH : Def H) (hS : Def S) (he : Def e)
    (s : TableauSlot tm) : AddrDef (fun x a => rawTableauQuery tm (H x a) (S x a) (e x a) s) := by
  have hd := he.sub (hS.add (Def.lit 1))
  have hi : AddrDef (fun x a => match s with
      | .inl i => rawInitialQuery (S x a) (e x a) i
      | _ => (0,0)) := by
    rcases s with i | (i|u)
    · exact rawInitialQuery_def hS he i
    · exact AddrDef.const _
    · exact AddrDef.const _
  have hj : AddrDef (fun x a => match s with
      | .inr (.inl i) => rawStepQuery (S x a) ((e x a-(S x a+1))/(S x a+1))
          ((e x a-(S x a+1))%(S x a+1)) i
      | _ => (0,0)) := by
    rcases s with i | (i|u)
    · exact AddrDef.const _
    · exact rawStepQuery_def hS (hd.div (hS.add (Def.lit 1))) (hd.mod (hS.add (Def.lit 1))) i
    · exact AddrDef.const _
  have hk : AddrDef (fun x a => match s with
      | .inr (.inr _) => (H x a,rawCell (S x a) 0)
      | _ => (0,0)) := by
    rcases s with i | (i|u)
    · exact AddrDef.const _
    · exact AddrDef.const _
    · exact ⟨hH,rawCell_def hS (Def.lit 0)⟩
  apply (AddrDef.ite (PDef.lt he (hS.add (Def.lit 1))) hi
    (AddrDef.ite (PDef.lt hd (hH.mul (hS.add (Def.lit 1)))) hj hk)).congr
  intro x a
  dsimp [rawTableauQuery]
  split_ifs <;> rcases s with i | (i | u) <;> rfl

theorem rawTableauQuery_correct (tm : FinTM2) (H S : Nat) (e : Fin (eventCount H S))
    (s : TableauSlot tm) :
    rawTableauQuery tm H S e.val s =
      ((tableauQuery tm (decodeEvent H S e) s).1.val,(tableauQuery tm (decodeEvent H S e) s).2.val) := by
  unfold rawTableauQuery decodeEvent
  split_ifs with hi hs
  · rcases s with i | (i | u)
    · exact rawInitialQuery_eq (H:=H) (S:=S) ⟨e.val,hi⟩ i
    · rfl
    · rfl
  · rcases s with i | (i | u)
    · rfl
    · simpa only [tableauQuery,finProdFinEquiv_symm_apply,Fin.divNat,Fin.modNat] using
        rawStepQuery_eq (finProdFinEquiv.symm ⟨e.val-(S+1),hs⟩).1
          (finProdFinEquiv.symm ⟨e.val-(S+1),hs⟩).2 i
    · rfl
  · rcases s with i | (i | u)
    · rfl
    · rfl
    · simp [tableauQuery,rawCell_eq]

def rawQuery (V : NPVerifier) (s : FixedSlot V) (x : List Bool) (e : Nat) : Nat :=
  let w := (alphabetCodec V).width
  match s with
  | .inl (s,b) =>
    let p := rawTableauQuery V.computation.tm (horizon V x.length) (capacity V x.length) e s
    (p.1*(capacity V x.length+1)+p.2)*w+b.val
  | .inr _ => (Classical.choice (codec_width_nonempty V)).val

theorem rawQuery_def (V : NPVerifier) (s : FixedSlot V) :
    Def (r:=1) (fun x a => rawQuery V s x (a 0)) := by
  rcases s with ⟨s,b⟩ | u
  · have hp := rawTableauQuery_def V.computation.tm (horizon_def V) (capacity_def V) (Def.arg (0 : Fin 1)) s
    exact (((hp.1.mul ((capacity_def V).add (Def.lit 1))).add hp.2).mul
      (Def.lit (alphabetCodec V).width)).add (Def.lit b.val)
  · exact Def.lit _

theorem rawQuery_correct (V : NPVerifier) (x : List Bool) (e : Fin (canonicalVerifier V x).events)
    (i : Fin (queryNumber V)) :
    rawQuery V ((slotIndex V).symm i) x e.val = ((canonicalVerifier V x).query e i).val := by
  change Fin (eventCount (horizon V x.length) (capacity V x.length)) at e
  unfold canonicalVerifier
  rw [variableIndex_val]
  generalize hs : (slotIndex V).symm i = s
  rcases s with ⟨s,b⟩ | u
  · dsimp [rawQuery,LocalCSP.padAt,LocalCSP.booleanize,tests,tableau]
    rw [rawTableauQuery_correct V.computation.tm _ _ e s]
  · simp [rawQuery,LocalCSP.padAt]

end NPTableau
end DirectedFeedback.CookLevin

end
end

section

noncomputable section
open scoped Classical
namespace DirectedFeedback.CookLevin.NPTableau
open BoundedExpr Turing DFVSGames.Foundations.PCP
attribute [local instance] FinTM2.ΛFin FinTM2.kFin FinTM2.σFin

def decodedPattern (V : NPVerifier) (p : VerifierToCNF.Pattern (queryNumber V))
    (s : TableauSlot V.computation.tm) : Atom V.computation.tm.Γ V.computation.tm.Λ V.computation.tm.σ :=
  (alphabetCodec V).decode (fun b => p (slotIndex V (.inl (s,b))))

def rawAccepts (V : NPVerifier) (p : VerifierToCNF.Pattern (queryNumber V)) (x : List Bool) (e : Nat) : Bool :=
  let H := horizon V x.length
  let S := capacity V x.length
  let a := decodedPattern V p
  if e < S+1 then rawInitialAccepts V x e (a ∘ Sum.inl)
  else if e-(S+1) < H*(S+1) then
    rawStepAccepts V.computation.tm.m S ((e-(S+1))%(S+1)) (a ∘ Sum.inr ∘ Sum.inl)
  else decide ((a (.inr (.inr ()))).2 V.computation.tm.k₁ = some (V.computation.outputAlphabet.invFun true))

theorem rawAccepts_def (V : NPVerifier) (p : VerifierToCNF.Pattern (queryNumber V)) :
    FDef (r:=1) (fun x a => rawAccepts V p x (a 0)) := by
  have hS := (capacity_def (r:=1) V).add (Def.lit 1)
  have hd := (Def.arg (0 : Fin 1)).sub hS
  have hh := (PDef.lt (Def.arg (0 : Fin 1)) hS).ite
    (rawInitialAccepts_def V (Def.arg 0) (decodedPattern V p ∘ Sum.inl))
    ((PDef.lt hd ((horizon_def V).mul hS)).ite
      (rawStepAccepts_def V.computation.tm.m (capacity_def V) (hd.mod hS)
        (decodedPattern V p ∘ Sum.inr ∘ Sum.inl))
        (FDef.const (decide (((decodedPattern V p) (.inr (.inr ()))).2 V.computation.tm.k₁ =
          some (V.computation.outputAlphabet.invFun true)))))
  apply hh.congr
  intro x a
  dsimp [rawAccepts]
  split_ifs <;> rfl

theorem rawAccepts_correct (V : NPVerifier) (x : List Bool)
    (e : Fin (canonicalVerifier V x).events) (p : VerifierToCNF.Pattern (queryNumber V)) :
    rawAccepts V p x e.val = (canonicalVerifier V x).accepts e p := by
  change Fin (eventCount (horizon V x.length) (capacity V x.length)) at e
  unfold rawAccepts canonicalVerifier
  dsimp [LocalCSP.padAt,LocalCSP.booleanize,tests,tableau]
  unfold decodeEvent
  split_ifs with hi hs
  · exact rawInitialAccepts_eq V x ⟨e.val,hi⟩ _
  · have hh := rawStepAccepts_eq V.computation.tm.m
        (finProdFinEquiv.symm ⟨e.val-(capacity V x.length+1),hs⟩).2
          (decodedPattern V p ∘ Sum.inr ∘ Sum.inl)
    apply hh.trans
    apply Bool.eq_iff_iff.mpr
    simp only [stepAccepts,decide_eq_true_eq]
    rfl
  · rfl

def family (V : NPVerifier) : CNFPrinter.Family (queryNumber V) where
  verifier := canonicalVerifier V
  variables_def := (((horizon_def V).add (Def.lit 1)).mul
    ((capacity_def V).add (Def.lit 1))).mul (Def.lit _)
  events_def := (((capacity_def V).add (Def.lit 1)).add
    ((horizon_def V).mul ((capacity_def V).add (Def.lit 1)))).add (Def.lit 1)
  query := fun i => rawQuery V ((slotIndex V).symm i)
  query_def := fun i => rawQuery_def V ((slotIndex V).symm i)
  query_correct := rawQuery_correct V
  accepts := rawAccepts V
  accepts_def := rawAccepts_def V
  accepts_correct := rawAccepts_correct V

noncomputable def computation (V : NPVerifier) : TM2ComputableInPolyTime
    (id : List Bool → List Bool) DFVSGames.Foundations.Complexity.formulaBits (canonicalFormula V) :=
  (family V).computation (queryNumber_ge V)

theorem computation_finite (V : NPVerifier) : FiniteAlphabet (computation V).tm :=
  (family V).computation_finite (queryNumber_ge V)

end DirectedFeedback.CookLevin.NPTableau

end
end

section

noncomputable section
open scoped Classical
namespace DirectedFeedback.BinaryEmbed
open DFVSGames DFVSGames.Foundations

def name : Nat → Nat
  | 0 => 0
  | n+1 => Nat.bit true (name n)

theorem name_bits (n : Nat) : (name n).bits=List.replicate n true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [name,Nat.bits_append_bit _ true (by simp),ih,List.replicate_succ]

theorem name_injective : Function.Injective name := by
  intro i j h
  have hh := congrArg (fun n => n.bits.length) h
  simpa only [name_bits,List.length_replicate] using hh

def literal {n : Nat} (l : Target.Literal n) : BinaryFormula.Literal := ⟨name l.variableIndex.val,l.positive⟩
def clause {n : Nat} (c : Target.Clause n) : BinaryFormula.Clause := c.map literal
def formula (F : Target.Formula) : BinaryFormula.Formula := ⟨F.clauses.map clause⟩

theorem literal_eval {n : Nat} (l : Target.Literal n) (a : Nat → Bool) :
    (literal l).eval a=l.eval (fun i => a (name i.val)) := rfl

theorem clause_eval {n : Nat} (c : Target.Clause n) (a : Nat → Bool) :
    (clause c).eval a=c.eval (fun i => a (name i.val)) := by
  simp [clause,BinaryFormula.Clause.eval,Target.Clause.eval,literal_eval]

theorem satisfiable_iff (F : Target.Formula) : (formula F).Satisfiable ↔ F.Satisfiable := by
  constructor
  · rintro ⟨a,ha⟩
    refine ⟨fun i => a (name i.val),?_⟩
    intro c hc
    rw [← clause_eval]
    exact ha _ (List.mem_map.mpr ⟨c,hc,rfl⟩)
  · rintro ⟨a,ha⟩
    let f : Fin F.«variables» → Nat := fun i => name i.val
    have hf : Function.Injective f := fun i j h => Fin.ext (name_injective h)
    let b : Nat → Bool := Function.extend f a (fun _ => false)
    have hb : ∀ i, b (name i.val)=a i := fun i => hf.extend_apply a _ i
    refine ⟨b,?_⟩
    intro c hc
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
    rw [clause_eval]
    simpa only [hb] using ha d hd

theorem frame_replicate (n : Nat) : BinaryEncoding.frame (List.replicate n true)=
    List.replicate (2*n) true ++ [false] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ,BinaryEncoding.frame,ih]
    have h : 2*(n+1)=2*n+1+1 := by omega
    simp [h,List.replicate_succ]

theorem literal_bits {n : Nat} (l : Target.Literal n) :
    BinaryEncoding.literalBits (literal l) = l.positive :: (List.replicate (2*l.variableIndex.val) true ++ [false]) := by
  simp [BinaryEncoding.literalBits,BinaryEncoding.nameBits,literal,name_bits,frame_replicate]

def clauseBody {n : Nat} (c : Target.Clause n) : List Bool := true :: BinaryEncoding.clauseBits (clause c)

theorem formula_bits (F : Target.Formula) :
    BinaryEncoding.formulaBits (formula F)=F.clauses.flatMap clauseBody ++ [false] := by
  change BinaryEncoding.clausesBits (F.clauses.map clause)=_
  generalize F.clauses=cs
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [BinaryEncoding.clausesBits,clauseBody,ih]

end DirectedFeedback.BinaryEmbed

end
end

section

noncomputable section
open scoped Classical
namespace DirectedFeedback.BoundedExpr
open DFVSGames.Foundations DFVSGames.Foundations.PCP DFVSGames.Foundations.Complexity
namespace BinaryCNFPrinter

abbrev Lit := Nat × Bool

def literalBits (l : Lit) : List Bool := l.2 :: (List.replicate (2*l.1) true ++ [false])
def clauseBits (a b c : Lit) : List Bool := true :: (literalBits a ++ literalBits b ++ literalBits c)

def rawSplit : List Lit → List Nat → List Bool
  | [a,b,c], [] => clauseBits a b c
  | a::b::rest, y::ys => clauseBits a b (y,true) ++ rawSplit ((y,false)::rest) ys
  | _, _ => []

theorem clauseBits_eq {n : Nat} (a b c : Target.Literal n) :
    clauseBits (a.variableIndex.val,a.positive) (b.variableIndex.val,b.positive)
      (c.variableIndex.val,c.positive) = BinaryEmbed.clauseBody #v[a,b,c] := by
  simp [clauseBits,literalBits,BinaryEmbed.clauseBody,DFVSGames.BinaryEncoding.clauseBits,
    BinaryEmbed.clause,BinaryEmbed.literal_bits]

theorem rawSplit_eq {n : Nat} (ls : List (Target.Literal n)) (ys : List (Fin n)) :
    rawSplit (ls.map (fun l => (l.variableIndex.val,l.positive))) (ys.map Fin.val) =
      (VerifierToCNF.splitLong ls ys).flatMap BinaryEmbed.clauseBody := by
  induction ys generalizing ls with
  | nil =>
    match ls with
    | [] => rfl
    | [_] => rfl
    | [_,_] => rfl
    | [a,b,c] => simpa only [rawSplit,VerifierToCNF.splitLong,List.map_cons,List.map_nil,
        List.flatMap_cons,List.flatMap_nil,List.append_nil] using clauseBits_eq a b c
    | _::_::_::_::_ => rfl
  | cons y ys ih =>
    match ls with
    | [] => rfl
    | [_] => rfl
    | a::b::rest =>
      simp only [List.map_cons,rawSplit,VerifierToCNF.splitLong,List.flatMap_cons]
      apply congrArg₂ List.append
      · exact clauseBits_eq a b ⟨y,true⟩
      · simpa only [List.map_cons] using ih (⟨y,false⟩::rest)

theorem literalBits_def {r : Nat} {n : List Bool → (Fin r → Nat) → Nat} (hn : Def n) (b : Bool) :
    OutDef (fun x a => literalBits (n x a,b)) := by
  simpa only [literalBits,List.singleton_append] using
    (OutDef.bit b).append (OutDef.nat ((Def.lit 2).mul hn))

theorem clauseBits_def {r : Nat} {f g h : List Bool → (Fin r → Nat) → Nat}
    (hf : Def f) (hg : Def g) (hh : Def h) (a b c : Bool) :
    OutDef (fun x v => clauseBits (f x v,a) (g x v,b) (h x v,c)) :=
  by
    simpa only [clauseBits,List.singleton_append] using (OutDef.bit true).append
      (((literalBits_def hf a).append (literalBits_def hg b)).append (literalBits_def hh c))

theorem rawSplit_def {r : Nat}
    (ls : List ((List Bool → (Fin r → Nat) → Nat) × Bool))
    (ys : List (List Bool → (Fin r → Nat) → Nat))
    (hls : ∀ l ∈ ls, Def l.1) (hys : ∀ y ∈ ys, Def y) :
    OutDef (fun x a => rawSplit (ls.map (fun l => (l.1 x a,l.2))) (ys.map (fun y => y x a))) := by
  induction ys generalizing ls with
  | nil =>
    match ls with
    | [] => exact OutDef.nil
    | [_] => exact OutDef.nil
    | [_,_] => exact OutDef.nil
    | [a,b,c] => exact clauseBits_def (hls a (by simp)) (hls b (by simp)) (hls c (by simp)) a.2 b.2 c.2
    | _::_::_::_::_ => exact OutDef.nil
  | cons y ys ih =>
    match ls with
    | [] => exact OutDef.nil
    | [_] => exact OutDef.nil
    | a::b::rest =>
      have hy := hys y (by simp)
      have ht := ih ((y,false)::rest) (by
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact hy
        · exact hls c (by simp [hc])) (fun z hz => hys z (by simp [hz]))
      simpa only [List.map_cons,rawSplit] using
        (clauseBits_def (hls a (by simp)) (hls b (by simp)) hy a.2 b.2 true).append ht

abbrev Family := CNFPrinter.Family

namespace Family
variable {q : Nat} (F : Family q) (hq : 3≤q)

def blockBits (x : List Bool) (e : Nat) (p : VerifierToCNF.PatternIndex q) : List Bool :=
  let bits := VerifierToCNF.patternAt q p
  if F.accepts bits x e then
    (List.replicate (q-2) (clauseBits (F.query ⟨0,by omega⟩ x e,true)
      (F.query ⟨0,by omega⟩ x e,false) (F.query ⟨0,by omega⟩ x e,true))).flatten
  else rawSplit
    ((List.ofFn (fun i => (F.query i x e,!(bits i)))))
    (List.ofFn (fun j : Fin (q-3) => (F.verifier x).«variables»+
      ((e*(VerifierToCNF.patterns q).length+p.val)*(q-3)+j.val)))

def eventBits (x : List Bool) (e : Nat) : List Bool :=
  (List.finRange (VerifierToCNF.patterns q).length).flatMap (blockBits F hq x e)

def bits (x : List Bool) : List Bool :=
  (List.range (F.verifier x).events).flatMap (eventBits F hq x) ++ [false]

theorem blockBits_def (p : VerifierToCNF.PatternIndex q) :
    OutDef (r:=1) (fun x a => blockBits F hq x (a 0) p) := by
  have hv := F.variables_def.rename (Fin.elim0 : Fin 0 → Fin 1)
  have hf (j : Fin (q-3)) : Def (r:=1) (fun x a => (F.verifier x).«variables»+
      (((a 0)*(VerifierToCNF.patterns q).length+p.val)*(q-3)+j.val)) :=
    hv.add ((((Def.arg 0).mul (Def.lit _)).add (Def.lit _)).mul (Def.lit _) |>.add (Def.lit _))
  have hs := rawSplit_def
    (List.ofFn (fun i : Fin q => ((fun x (a : Fin 1 → Nat) => F.query i x (a 0)),
      !(VerifierToCNF.patternAt q p i))))
    (List.ofFn (fun j : Fin (q-3) => fun x (a : Fin 1 → Nat) => (F.verifier x).«variables»+
      (((a 0)*(VerifierToCNF.patterns q).length+p.val)*(q-3)+j.val)))
    (by intro l hl; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hl; exact F.query_def i)
    (by intro y hy; obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hy; exact hf j)
  have ht := OutDef.flatMap (List.replicate (q-2) ())
    (fun _ x (a : Fin 1 → Nat) => clauseBits (F.query ⟨0,by omega⟩ x (a 0),true)
      (F.query ⟨0,by omega⟩ x (a 0),false) (F.query ⟨0,by omega⟩ x (a 0),true))
    (fun _ _ => clauseBits_def (F.query_def _) (F.query_def _) (F.query_def _) true false true)
  apply (OutDef.ite (F.accepts_def (VerifierToCNF.patternAt q p) |>.bool_true) ht hs).congr
  intro x a
  simp [blockBits,List.map_ofFn,List.flatMap_replicate,Function.comp_def]

theorem eventBits_def : OutDef (r:=1) (fun x a => eventBits F hq x (a 0)) :=
  OutDef.flatMap _ (fun p x a => blockBits F hq x (a 0) p) (fun p _ => blockBits_def F hq p)

theorem bits_def : OutDef (r:=0) (fun x _ => bits F hq x) := by
  apply ((OutDef.loop F.events_def (eventBits_def F hq)).append (OutDef.bit false)).congr
  intro x a
  simp [bits]

end Family
end BinaryCNFPrinter
end DirectedFeedback.BoundedExpr

end
end

section

noncomputable section
open scoped Classical
namespace DirectedFeedback.BoundedExpr.BinaryCNFPrinter
open DFVSGames.Foundations DFVSGames.Foundations.PCP DFVSGames.Foundations.Complexity

namespace Family
variable {q : Nat} (F : Family q) (hq : 3≤q)

theorem blockBits_correct (x : List Bool) (e : Fin (F.verifier x).events)
    (p : VerifierToCNF.PatternIndex q) :
    blockBits F hq x e.val p = (VerifierToCNF.block (F.verifier x) hq e p).flatMap BinaryEmbed.clauseBody := by
  unfold blockBits VerifierToCNF.block
  dsimp only
  rw [F.accepts_correct x e]
  split
  · have he : clauseBits (F.query ⟨0,by omega⟩ x e.val,true)
        (F.query ⟨0,by omega⟩ x e.val,false) (F.query ⟨0,by omega⟩ x e.val,true) =
        BinaryEmbed.clauseBody (VerifierToCNF.tautology (F.verifier x) hq e) := by
      simp only [VerifierToCNF.tautology]
      rw [← clauseBits_eq]
      simp [VerifierToCNF.oldIndex,F.query_correct]
    rw [List.flatMap_replicate,← he]
  · rw [← rawSplit_eq]
    apply congrArg₂ rawSplit
    · simp only [VerifierToCNF.forbiddenClause,List.map_ofFn]
      congr 1
      funext i
      simp [VerifierToCNF.liftLiteral,VerifierToCNF.forbiddenLiteral,VerifierToCNF.oldIndex,F.query_correct]
    · simp only [VerifierToCNF.auxiliaryNames,List.map_ofFn]
      congr 1
      funext j
      exact (VerifierToCNF.freshIndex_value _ _ _ _).symm

theorem eventBits_correct (x : List Bool) (e : Fin (F.verifier x).events) :
    eventBits F hq x e.val = (VerifierToCNF.eventBlock (F.verifier x) hq e).flatMap BinaryEmbed.clauseBody := by
  simp only [eventBits,VerifierToCNF.eventBlock,List.flatMap_assoc]
  congr 1
  funext p
  exact blockBits_correct F hq x e p

theorem bits_correct (x : List Bool) :
    bits F hq x = DFVSGames.BinaryEncoding.formulaBits
      (BinaryEmbed.formula (VerifierToCNF.convert (F.verifier x) hq)) := by
  rw [BinaryEmbed.formula_bits]
  unfold bits
  apply congrArg₂ List.append
  · change (List.range (F.verifier x).events).flatMap (eventBits F hq x) =
      (((List.finRange (F.verifier x).events).flatMap
        (VerifierToCNF.eventBlock (F.verifier x) hq)).flatMap BinaryEmbed.clauseBody)
    rw [List.flatMap_assoc]
    exact CNFPrinter.range_flatMap _ _ (eventBits_correct F hq x)
  · rfl

noncomputable def computation : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool)
    DFVSGames.BinaryEncoding.formulaBits
    (fun x => BinaryEmbed.formula (VerifierToCNF.convert (F.verifier x) hq)) := by
  let o := Classical.choose (bits_def F hq)
  have ho : ∀ x, o.eval x Fin.elim0 = DFVSGames.BinaryEncoding.formulaBits
      (BinaryEmbed.formula (VerifierToCNF.convert (F.verifier x) hq)) := by
    intro x
    exact (Classical.choose_spec (bits_def F hq) x Fin.elim0).trans (bits_correct F hq x)
  exact Output.realizes _ _ o ho

theorem computation_finite (k : (computation F hq).tm.K) : Finite ((computation F hq).tm.Γ k) := by
  unfold computation
  exact Output.realizes_alphabet _ _ _ _ k

end Family
end DirectedFeedback.BoundedExpr.BinaryCNFPrinter

end
end

section

noncomputable section
namespace DirectedFeedback.CookLevin.NPTableau
open Turing DFVSGames.Foundations.Complexity BoundedExpr
open DFVSGames.Explicit.MachineOutputContract

def binaryFormula (V : NPVerifier) (input : List Bool) : DFVSGames.BinaryFormula.Formula :=
  BinaryEmbed.formula (canonicalFormula V input)

def binaryInput (V : NPVerifier) (input : List Bool) : List Bool :=
  DFVSGames.BinaryEncoding.formulaBits (binaryFormula V input)

theorem binaryInput_correct (V : NPVerifier) (input : List Bool) :
    DFVSGames.BinaryLanguage.language (binaryInput V input) ↔ V.Accepts input := by
  rw [binaryInput,DFVSGames.BinaryLanguage.language_encoded,binaryFormula,
    BinaryEmbed.satisfiable_iff,canonicalFormula_correct]

def binaryComputation (V : NPVerifier) : TM2ComputableInPolyTime (id : List Bool → List Bool)
    (id : List Bool → List Bool) (binaryInput V) := by
  let c := BinaryCNFPrinter.Family.computation (family V) (queryNumber_ge V)
  exact {
    tm := c.tm
    inputAlphabet := c.inputAlphabet
    outputAlphabet := c.outputAlphabet
    time := c.time
    outputsFun := c.outputsFun }

theorem binaryComputation_finite (V : NPVerifier) : FiniteAlphabet (binaryComputation V).tm :=
  BinaryCNFPrinter.Family.computation_finite (family V) (queryNumber_ge V)

def sourceComputation (V : NPVerifier) {ε δ : ℝ} (S : BinaryGapReduction ε δ) :
    TM2ComputableInPolyTime (id : List Bool → List Bool) gameBits
      (fun input => S.construct (binaryInput V input)) :=
  MachineSequential.composeBits (binaryComputation V) S.computation

theorem sourceComputation_finite (V : NPVerifier) {ε δ : ℝ}
    (S : BinaryGapReduction ε δ) : FiniteAlphabet (sourceComputation V S).tm :=
  MachineFiniteAlphabet.composeBits (binaryComputation V) S.computation
    (binaryComputation_finite V) S.finiteAlphabet

end DirectedFeedback.CookLevin.NPTableau

end
end

section

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback
open Construction Games PacketSeeds SourceProbability FiniteDistribution RankGraph
open DFVSGames.Foundations DFVSGames.Foundations.Target DFVSGames.Foundations.Complexity
open DFVSGames.Explicit.MachineOutputContract

namespace RawFamily
variable {D : Nat} (P : Parameters D) (S : BinaryGapReduction P.theta P.theta)
local instance reductionAlphabetNeZero : NeZero S.alphabet :=
  ⟨by have := S.alphabetAtLeastTwo; omega⟩
variable (R : RankParameters P (X S.alphabet)) [NeZero R.N]
variable (C : Nat) (c : Seed S.alphabet P.M P.T R.N → Nat) (hC : 0<C)
variable (hc : ∀ s, (C:ℝ)*mass R.law (8*(D+1)) P.K s=c s)

def gameComputation : Turing.TM2ComputableInPolyTime gameBits GapInstance.bits
    (fun I : Instance S.alphabet => (family S.alphabet P.M P.T R.N D C c hC).printer.inst (gameBits I)) := by
  let computation := (family S.alphabet P.M P.T R.N D C c hC).printer.computation
  exact {
    tm := computation.tm
    inputAlphabet := computation.inputAlphabet
    outputAlphabet := computation.outputAlphabet
    time := computation.time
    outputsFun := fun I => computation.outputsFun (gameBits I) }

theorem gameComputation_finite : FiniteAlphabet (gameComputation P S R C c hC).tm :=
  (family S.alphabet P.M P.T R.N D C c hC).printer.computation_finite

variable (A : ℝ) (hA : 4*A≤D) (language : List Bool → Prop) (V : NPVerifier)
variable (hV : ∀ x, language x ↔ V.Accepts x)

def reduction : GapReduction A language where
  construct x := (family S.alphabet P.M P.T R.N D C c hC).printer.inst
    (gameBits (S.construct (CookLevin.NPTableau.binaryInput V x)))
  computation := MachineSequential.composeBits
    (f := fun x => S.construct (CookLevin.NPTableau.binaryInput V x))
    (g := fun I => (family S.alphabet P.M P.T R.N D C c hC).printer.inst (gameBits I))
    (CookLevin.NPTableau.sourceComputation V S) (gameComputation P S R C c hC)
  finiteAlphabet := MachineFiniteAlphabet.composeBits (CookLevin.NPTableau.sourceComputation V S)
    (gameComputation P S R C c hC) (CookLevin.NPTableau.sourceComputation_finite V S)
    (gameComputation_finite P S R C c hC)
  completeness x hx := encoded_yes P S R C c hC hc _
    ((CookLevin.NPTableau.binaryInput_correct V x).mpr ((hV x).mp hx))
  soundness x hx := encoded_no P S R C c hC hc A hA _ (by
    intro hb
    exact hx ((hV x).mpr ((CookLevin.NPTableau.binaryInput_correct V x).mp hb)))
end RawFamily

theorem rankSize_pos {D : Nat} (P : Parameters D) (X : Type) [Fintype X]
    (R : RankParameters P X) : 0<R.N := by
  obtain ⟨ψ⟩ := R.law.support_nonempty
  have hL : 0<rankLength X P.T := by unfold rankLength; omega
  exact (ψ.val.val ⟨0,hL⟩).isLt |> (fun h => lt_of_le_of_lt (Nat.zero_le _) h)

theorem main : MainStatement := by
  intro A _ language hNP
  obtain ⟨V,hV⟩ := hNP
  obtain ⟨D,hD⟩ := exists_nat_ge (4*A)
  obtain ⟨P⟩ := exists_parameters D
  obtain ⟨S⟩ := DFVSGames.theorem11 P.theta P.theta
    (by exact_mod_cast P.theta_pos) P.theta_half (by exact_mod_cast P.theta_pos) P.theta_half
  let : NeZero S.alphabet := ⟨by have := S.alphabetAtLeastTwo; omega⟩
  obtain ⟨R⟩ := exists_rankParameters P (RawFamily.X S.alphabet)
  let : NeZero R.N := ⟨ne_of_gt (rankSize_pos P _ R)⟩
  obtain ⟨C,hC,c,hc⟩ := PacketSeeds.denominator (Y:=RawFamily.Y S.alphabet) (M:=P.M)
    R.law R.rational (8*(D+1)) P.K
  exact ⟨RawFamily.reduction P S R C c hC hc A hD language V hV⟩

end DirectedFeedback

end
end

end OAI
