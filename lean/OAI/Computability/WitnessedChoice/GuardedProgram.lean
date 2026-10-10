import OAI.Computability.WitnessedChoice.QuotedSyntax

namespace OAI

noncomputable section


namespace WitnessedChoice.BGS
open Classical WitnessedSeparation WitnessedSeparation.Hereditary


namespace QuotedTerm
open RelationPools

section

variable {n : ℕ}

def witnessRelations (B : ℕ) (valid : QuotedFormula n) (x C : QuotedTerm n) : QuotedTerm n :=
  cond valid
    (identity.singleton.cup ((localRelations B).bind
      (C.up.comprehend (composition (.var 1) (.var 0))
        (.filter x.up.up (composition (.var 1) (.var 0)))))) identity.singleton

def guardedChoice (D M : QuotedTerm n) : QuotedTerm n :=
  cond ((QuotedFormula.eq D .empty).neg.and
      (.allIn D (.allIn D.up
        (.existsIn M.up.up (.link (.var 2) (.var 1) (.var 0)))))) D empty.singleton

def selectionStep (x y : QuotedTerm n) : QuotedTerm n :=
  x.cup ((y.double y.unique).inter edgeAtoms)

variable {A : Type} [Fintype A] (S : Input A) (env : Fin n → HF A)

@[simp] lemma meaning_cond (g : QuotedFormula n) (a b : QuotedTerm n) :
    (cond g a b).meaning S env = if g.meaning S env then a.meaning S env else b.meaning S env := rfl

lemma meaning_witnessRelations (B : ℕ) (valid : QuotedFormula n) (x C : QuotedTerm n)
    (X : Finset A) (cycles : Finset (Relation A))
    (hx : x.meaning S env = stateCode X)
    (hC : C.meaning S env = ofFinset (cycles.image relationCode)) :
    (witnessRelations B valid x C).meaning S env =
      ofFinset ((witnessPool B S (valid.meaning S env) (fun _ => cycles) X).image permutationGraph) := by
  have hcomp (l c : Relation A) :
      (composition (var (1 : Fin (n+2))) (var 0)).meaning S
        (Fin.cons (relationCode c) (Fin.cons (relationCode l) env)) = relationCode (compose l c) :=
    meaning_composition S _ _ _ _ _ rfl rfl
  have hf (l c : Relation A) :
      (QuotedFormula.filter x.up.up (composition (var (1 : Fin (n+2))) (var 0))).meaning S
        (Fin.cons (relationCode c) (Fin.cons (relationCode l) env)) ↔ RawFilter S X (compose l c) :=
    QuotedFormula.meaning_filter S _ _ _ _ _ (by simpa using hx) (hcomp l c)
  simp only [witnessRelations,meaning_cond,witnessPool]
  split_ifs with hv
  · simp only [meaning_cup,meaning_singleton,identity,localRelations,meaning_bind,
      meaning_up,hC,elements_ofFinset,comprehend,Hereditary.singleton]
    apply ofFinset_inj.mpr
    ext z
    simp only [Finset.mem_union,Finset.mem_singleton,Finset.mem_biUnion,Finset.mem_image,
      Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert]
    constructor
    · rintro (hz | ⟨l,⟨r,hr,rfl⟩,c,⟨⟨t,ht,rfl⟩,hf'⟩,hz⟩)
      · exact ⟨1,Or.inl rfl,(hz.trans (relationCode_graph 1)).symm⟩
      · have hh := (hf r t).mp hf'
        obtain ⟨g,hg,hfg⟩ := (rawFilter_iff S X _).mp hh
        refine ⟨g,Or.inr ⟨hfg,r,hr,t,ht,hg⟩,?_⟩
        rw [hcomp r t,hg,relationCode_graph] at hz
        exact hz
    · rintro ⟨g,(rfl | ⟨hfg,r,hr,t,ht,hg⟩),rfl⟩
      · exact Or.inl (relationCode_graph 1).symm
      · refine Or.inr ⟨relationCode r,⟨r,hr,rfl⟩,relationCode t,⟨⟨t,ht,rfl⟩,?_⟩,?_⟩
        · exact (hf r t).mpr ((rawFilter_iff S X _).mpr ⟨g,hg,hfg⟩)
        · rw [hcomp r t,hg,relationCode_graph]
  · simp only [meaning_singleton,identity,relationCode_graph,Finset.image_singleton,Hereditary.singleton]

lemma meaning_guardedChoice (D M : QuotedTerm n) (P : Selection A) (X : Finset A)
    (hD : D.meaning S env = stateCode (P.candidates X))
    (hM : M.meaning S env = ofFinset ((P.witnesses X).image permutationGraph)) :
    (guardedChoice D M).meaning S env = ofFinset ((P.choices X).image choiceCode) := by
  have hne : stateCode (P.candidates X) ≠ emptyHF ↔ (P.candidates X).Nonempty := by
    change stateCode (P.candidates X) ≠ stateCode ∅ ↔ _
    simp only [ne_eq,stateCode_inj,Finset.nonempty_iff_ne_empty]
  have hm (a b : A) :
      (∃ g ∈ (P.witnesses X), Hereditary.pair (atom a) (atom b) ∈ elements (permutationGraph g)) ↔
      ∃ g ∈ P.witnesses X, g a = b := by
    simp only [← relationCode_graph,pair_mem_relationCode,mem_graph]
  simp only [guardedChoice,meaning_cond,QuotedFormula.meaning_and,QuotedFormula.meaning_neg,
    QuotedFormula.meaning_eq,hD,meaning_empty,hne,QuotedFormula.meaning_allIn,
    all_stateCode,meaning_up,QuotedFormula.meaning_existsIn,hM,elements_ofFinset,
    QuotedFormula.meaning_link,meaning_var,Fin.cons_zero,Fin.cons_one,fin_cons_two,
    Finset.mem_image,exists_exists_and_eq_and,hm]
  unfold Selection.choices Selection.TransitiveAt
  split_ifs
  · simp only [stateCode,Finset.image_image,Function.comp_def,choiceCode]
  · simp only [meaning_singleton,meaning_empty,Finset.image_singleton,choiceCode,ordinal]
    rfl

end

variable {n : ℕ} {A : Type} [Fintype A] (S : Input A) (env : Fin n → HF A)

omit [Fintype A] in
@[simp] lemma uniqueHF_atom (a : A) : uniqueHF (atom a) = emptyHF := by
  unfold uniqueHF
  simp only [elements_atom]
  apply dite_eq_right
  simp

@[simp] lemma meaning_unique (x : QuotedTerm n) :
    x.unique.meaning S env = uniqueHF (x.meaning S env) := rfl

@[simp] lemma meaning_inter (x y : QuotedTerm n) :
    (x.inter y).meaning S env = ofFinset (elements (x.meaning S env) ∩ elements (y.meaning S env)) := by
  simp only [inter,meaning_filter,QuotedFormula.meaning_mem,meaning_var,meaning_up,
    Fin.cons_zero,Finset.filter_mem_eq_inter]

lemma meaning_selectionStep (x y : QuotedTerm n) (X : Finset A) (c : Option A)
    (hx : x.meaning S env = stateCode X) (hy : y.meaning S env = choiceCode c)
    (hc : ∀ a, c = some a → a ∈ WitnessedChoice.edgeAtoms S) :
    (selectionStep x y).meaning S env = stateCode (Selection.advance X c) := by
  have hne (a : A) : (emptyHF : HF A) ≠ atom a := by
    intro h
    have hh := congrArg isSet h
    simp [emptyHF] at hh
  simp only [selectionStep,meaning_cup,hx,meaning_inter,meaning_double,meaning_unique,hy,
    meaning_edgeAtoms,elements_ofFinset]
  cases c with
  | none =>
    simp only [choiceCode,show ordinal (A := A) 0 = emptyHF from rfl,uniqueHF_empty,Hereditary.double,elements_ofFinset,
      stateCode,Selection.advance]
    apply ofFinset_inj.mpr
    ext z
    simp only [Finset.mem_union,Finset.mem_inter,Finset.mem_insert,Finset.mem_singleton,
      Finset.mem_image]
    constructor
    · rintro (h | ⟨(rfl|rfl),a,ha,he⟩)
      · exact h
      all_goals exact (hne a he.symm).elim
    · exact Or.inl
  | some a =>
    have ha := hc a rfl
    simp only [choiceCode,uniqueHF_atom,Hereditary.double,elements_ofFinset,stateCode,
      Selection.advance,Finset.image_insert]
    apply ofFinset_inj.mpr
    ext z
    simp only [Finset.mem_union,Finset.mem_inter,Finset.mem_insert,Finset.mem_singleton,
      Finset.mem_image]
    constructor
    · rintro (h | ⟨(rfl|rfl),b,hb,he⟩)
      · exact Or.inr h
      · exact Or.inl rfl
      · exact (hne b he.symm).elim
    · rintro (rfl|h)
      · exact Or.inr ⟨Or.inl rfl,a,ha,rfl⟩
      · exact Or.inl h

end QuotedTerm


namespace QuotedTerm

variable {n : ℕ}

def triple (a b c : QuotedTerm n) : QuotedTerm n := a.pair (b.pair c)

def successor (a : QuotedTerm n) : QuotedTerm n := a.cup a.singleton

def indices : QuotedTerm n := atoms.card.successor

end QuotedTerm

namespace QuotedFormula

variable {n : ℕ}

def incident (v e : QuotedTerm n) : QuotedFormula n :=
  existsIn v (existsIn e.up (input .I (.var 1) (.var 0)))

def adjacent (J u w : QuotedTerm n) : QuotedFormula n :=
  (eq u w).neg.and (existsIn J ((incident u.up (.var 0)).and (incident w.up (.var 0))))

end QuotedFormula

namespace QuotedTerm

variable {n : ℕ}

def distanceBase (V : QuotedTerm n) : QuotedTerm n := V.map (triple (.var 0) (.var 0) .empty)

def distanceFresh (V J R : QuotedTerm n) : QuotedTerm n :=
  V.bind (V.up.bind ((indices.filter
    ((QuotedFormula.mem (successor (.var 0)) indices).and
      (.existsIn V.up.up.up
        ((QuotedFormula.mem (triple (.var 3) (.var 0) (.var 1)) R.up.up.up.up).and
          ((QuotedFormula.eq (.var 0) (.var 2)).or
            (.adjacent J.up.up.up.up (.var 0) (.var 2))))))).map
              (triple (.var 2) (.var 1) (successor (.var 0)))))

def distanceStep (V J R : QuotedTerm n) : QuotedTerm n :=
  (R.cup (distanceBase V)).cup (distanceFresh V J R)

def tripleDomain (V : QuotedTerm n) : QuotedTerm n :=
  V.bind (V.up.bind (indices.map (triple (.var 2) (.var 1) (.var 0))))

variable {A : Type} [Fintype A] (S : Input A) (env : Fin n → HF A)

@[simp] lemma meaning_triple (a b c : QuotedTerm n) :
    (triple a b c).meaning S env = Hereditary.pair (a.meaning S env)
      (Hereditary.pair (b.meaning S env) (c.meaning S env)) := by simp [triple]

@[simp] lemma meaning_successor (a : QuotedTerm n) :
    a.successor.meaning S env = ofFinset (insert (a.meaning S env) (elements (a.meaning S env))) := by
  simp [successor,Hereditary.singleton]

@[simp] lemma meaning_card (a : QuotedTerm n) : a.card.meaning S env = cardHF (a.meaning S env) := rfl

@[simp] lemma meaning_indices : (indices : QuotedTerm n).meaning S env = ordinal (Fintype.card A+1) := by
  simp only [indices,meaning_successor,meaning_card,meaning_atoms,cardHF,stateCode,
    elements_ofFinset,Finset.card_image_of_injective _ atom_injective,Finset.card_univ,ordinal]

end QuotedTerm

namespace QuotedFormula

variable {n : ℕ} {A : Type} [Fintype A] (S : Input A) (env : Fin n → HF A)

@[simp] lemma meaning_incident (v e : QuotedTerm n) :
    (incident v e).meaning S env ↔ ∃ t ∈ elements (v.meaning S env),
      ∃ s ∈ elements (e.meaning S env), inputHF S .I t s = true := by simp [incident]

@[simp] lemma meaning_adjacent (J u w : QuotedTerm n) :
    (adjacent J u w).meaning S env ↔ u.meaning S env ≠ w.meaning S env ∧
      ∃ e ∈ elements (J.meaning S env),
        (∃ t ∈ elements (u.meaning S env), ∃ s ∈ elements e, inputHF S .I t s = true) ∧
        (∃ t ∈ elements (w.meaning S env), ∃ s ∈ elements e, inputHF S .I t s = true) := by
  simp [adjacent]

end QuotedFormula


structure CPTTerm (n : ℕ) where
  code : Term n
  count : code.wscCount = 0

structure CPTFormula (n : ℕ) where
  code : Formula n
  count : code.wscCount = 0

namespace CPTTerm

variable {n m : ℕ} {A : Type} [Fintype A]

def value (t : CPTTerm n) (S : Input A) (p : Polynomial ℝ) (env : Fin n → HF A) : HF A :=
  (t.code.total S p t.count env).choose

lemma eval_value (t : CPTTerm n) (S : Input A) (p : Polynomial ℝ) (env : Fin n → HF A) :
    t.code.eval S p env = some (t.value S p env) := (t.code.total S p t.count env).choose_spec

lemma value_eq (t : CPTTerm n) (S : Input A) (p : Polynomial ℝ) (env : Fin n → HF A) {x : HF A}
    (h : t.code.eval S p env = some x) : t.value S p env = x :=
  Option.some.inj ((t.eval_value S p env).symm.trans h)

def quoted (t : QuotedTerm n) : CPTTerm n := ⟨t.code,t.count⟩

def var (i : Fin n) : CPTTerm n := quoted (.var i)

def rename (t : CPTTerm n) (f : Fin n → Fin m) : CPTTerm m :=
  ⟨t.code.rename f,(t.code.rename_count f).trans t.count⟩

def up (t : CPTTerm n) : CPTTerm (n+1) := t.rename Fin.succ

def letIn (t : CPTTerm n) (b : CPTTerm (n+1)) : CPTTerm n :=
  ⟨t.code.letIn b.code,by simp only [Term.letIn,Term.singleton,Formula.truth,
    Term.wscCount,Formula.wscCount,t.count,b.count,Nat.add_zero]⟩

def iterate (b : CPTTerm (n+1)) : CPTTerm n := ⟨.iterate b.code,b.count⟩

@[simp] lemma value_quoted (t : QuotedTerm n) (S : Input A) (p : Polynomial ℝ) (env : Fin n → HF A) :
    (quoted t).value S p env = t.meaning S env := (quoted t).value_eq S p env (t.correct S p env)

@[simp] lemma value_var (i : Fin n) (S : Input A) (p : Polynomial ℝ) (env : Fin n → HF A) :
    (var i).value S p env = env i := value_quoted _ _ _ _

@[simp] lemma value_rename (t : CPTTerm n) (f : Fin n → Fin m) (S : Input A)
    (p : Polynomial ℝ) (env : Fin m → HF A) :
    (t.rename f).value S p env = t.value S p (env ∘ f) := by
  apply value_eq
  exact (t.code.eval_rename S p t.count f env).trans (t.eval_value S p _)

@[simp] lemma value_up (t : CPTTerm n) (S : Input A) (p : Polynomial ℝ) (env : Fin n → HF A) (x) :
    t.up.value S p (Fin.cons x env) = t.value S p env := value_rename _ _ _ _ _

@[simp] lemma value_letIn (t : CPTTerm n) (b : CPTTerm (n+1)) (S : Input A)
    (p : Polynomial ℝ) (env : Fin n → HF A) :
    (t.letIn b).value S p env = b.value S p (Fin.cons (t.value S p env) env) := by
  apply value_eq
  exact Term.eval_letIn S p t.code b.code env (t.eval_value S p env) (b.eval_value S p _)

lemma eval_iterate (b : CPTTerm (n+1)) (S : Input A) (p : Polynomial ℝ) (env : Fin n → HF A) :
    b.iterate.code.eval S p env = ordinaryIteration (resource p (Fintype.card A))
      (fun x => some (b.value S p (Fin.cons x env))) := by
  simp only [iterate,Term.eval,b.eval_value]

def unary (q : QuotedTerm (n+1)) (a : CPTTerm n) : CPTTerm n := a.letIn (quoted q)

def binary (q : QuotedTerm (n+2)) (a b : CPTTerm n) : CPTTerm n :=
  a.letIn (b.up.letIn (quoted q))

def distance (V J : CPTTerm n) : CPTTerm n :=
  V.letIn (J.up.letIn ((quoted (QuotedTerm.distanceStep (.var 2) (.var 1) (.var 0))).iterate))

end CPTTerm

namespace CPTFormula

variable {n m : ℕ} {A : Type} [Fintype A]

def value (t : CPTFormula n) (S : Input A) (p : Polynomial ℝ) (env : Fin n → HF A) : Bool :=
  (t.code.total S p t.count env).choose

lemma eval_value (t : CPTFormula n) (S : Input A) (p : Polynomial ℝ) (env : Fin n → HF A) :
    t.code.eval S p env = some (t.value S p env) := (t.code.total S p t.count env).choose_spec

lemma value_eq (t : CPTFormula n) (S : Input A) (p : Polynomial ℝ) (env : Fin n → HF A) {x : Bool}
    (h : t.code.eval S p env = some x) : t.value S p env = x :=
  Option.some.inj ((t.eval_value S p env).symm.trans h)

def quoted (t : QuotedFormula n) : CPTFormula n := ⟨t.code,t.count⟩

def rename (t : CPTFormula n) (f : Fin n → Fin m) : CPTFormula m :=
  ⟨t.code.rename f,(t.code.rename_count f).trans t.count⟩

def up (t : CPTFormula n) : CPTFormula (n+1) := t.rename Fin.succ

def letIn (t : CPTTerm n) (b : CPTFormula (n+1)) : CPTFormula n :=
  ⟨Formula.letIn t.code b.code,by simp only [Formula.letIn,Formula.existsIn,Term.singleton,
    Term.wscCount,Formula.wscCount,t.count,b.count,Nat.add_zero]⟩

@[simp] lemma value_quoted (t : QuotedFormula n) (S : Input A) (p : Polynomial ℝ) (env : Fin n → HF A) :
    (quoted t).value S p env = decide (t.meaning S env) := (quoted t).value_eq S p env (t.correct S p env)

@[simp] lemma value_rename (t : CPTFormula n) (f : Fin n → Fin m) (S : Input A)
    (p : Polynomial ℝ) (env : Fin m → HF A) :
    (t.rename f).value S p env = t.value S p (env ∘ f) := by
  apply value_eq
  exact (t.code.eval_rename S p t.count f env).trans (t.eval_value S p _)

@[simp] lemma value_up (t : CPTFormula n) (S : Input A) (p : Polynomial ℝ) (env : Fin n → HF A) (x) :
    t.up.value S p (Fin.cons x env) = t.value S p env := value_rename _ _ _ _ _

@[simp] lemma value_letIn (t : CPTTerm n) (b : CPTFormula (n+1)) (S : Input A)
    (p : Polynomial ℝ) (env : Fin n → HF A) :
    (letIn t b).value S p env = b.value S p (Fin.cons (t.value S p env) env) := by
  apply value_eq
  exact Formula.eval_letIn S p t.code b.code env (t.eval_value S p env) b.count (b.eval_value S p _)

end CPTFormula


namespace QuotedTerm

section

variable {n : ℕ}

def nat : ℕ → QuotedTerm n
  | 0 => empty
  | k+1 => successor (nat k)

def fst (a : QuotedTerm n) : QuotedTerm n :=
  ((a.filter (.eq (.card (.var 0)) (nat 1))).union).unique

def snd (a : QuotedTerm n) : QuotedTerm n :=
  cond (.eq a.union.card (nat 1)) a.fst
    ((a.union.diff a.fst.singleton).unique)

def component (a : QuotedTerm n) : ℕ → QuotedTerm n
  | 0 => a.fst
  | k+1 => (a.snd).component k

variable {A : Type} [Fintype A] (S : Input A) (env : Fin n → HF A)

@[simp] lemma meaning_union (a : QuotedTerm n) :
    a.union.meaning S env = unionHF (a.meaning S env) := rfl

@[simp] lemma meaning_diff (a b : QuotedTerm n) :
    (a.diff b).meaning S env = ofFinset ((elements (a.meaning S env)).filter
      fun z => z ∉ elements (b.meaning S env)) := by simp [diff]

@[simp] lemma meaning_nat (k : ℕ) : (nat (n := n) k).meaning S env = ordinal k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [nat,meaning_successor,ih,ordinal]

omit [Fintype A] in
lemma cardHF_singleton (a : HF A) : cardHF (Hereditary.singleton a) = ordinal 1 := by
  simp [cardHF,Hereditary.singleton]

omit [Fintype A] in
lemma cardHF_double_ne (a b : HF A) (h : a ≠ b) :
    cardHF (Hereditary.double a b) ≠ ordinal 1 := by
  simp only [cardHF,Hereditary.double,elements_ofFinset,Finset.card_insert_of_notMem
    (show a ∉ ({b} : Finset (HF A)) by simpa),Finset.card_singleton]
  exact fun hh => by have := ordinal_injective hh; contradiction

@[simp] lemma meaning_fst_pair (a b : QuotedTerm n) :
    (fst (a.pair b)).meaning S env = a.meaning S env := by
  let x := a.meaning S env
  let y := b.meaning S env
  simp only [fst,meaning_unique,meaning_union,meaning_filter,meaning_pair,
    QuotedFormula.meaning_eq,meaning_card,meaning_var,Fin.cons_zero,meaning_nat]
  change uniqueHF (unionHF (ofFinset ((elements (Hereditary.pair x y)).filter
    (fun z => cardHF z = ordinal 1)))) = x
  have hf : (elements (Hereditary.pair x y)).filter (fun z => cardHF z = ordinal 1) =
      {Hereditary.singleton x} := by
    by_cases h : x = y
    · rw [h]
      simp [Hereditary.pair,Hereditary.double,Hereditary.singleton,cardHF]
    · ext z
      simp only [Hereditary.pair,Hereditary.double,elements_ofFinset,Finset.mem_filter,
        Finset.mem_insert,Finset.mem_singleton]
      constructor
      · rintro ⟨hz,hc⟩
        rcases hz with rfl | rfl
        · rfl
        · exact (cardHF_double_ne x y h hc).elim
      · intro hz
        subst z
        exact ⟨Or.inl rfl,cardHF_singleton x⟩
  rw [hf]
  simp only [unionHF,elements_ofFinset,Finset.singleton_biUnion,Hereditary.singleton]
  exact uniqueHF_singleton x

@[simp] lemma meaning_snd_pair (a b : QuotedTerm n) :
    (snd (a.pair b)).meaning S env = b.meaning S env := by
  simp only [snd,cond,QuotedFormula.meaning_eq,meaning_card,meaning_union,meaning_pair,
    meaning_nat,meaning_fst_pair,meaning_diff,meaning_singleton,meaning_unique]
  let x := a.meaning S env
  let y := b.meaning S env
  have hu : unionHF (Hereditary.pair x y) = Hereditary.double x y := by
    simp [unionHF,Hereditary.pair,Hereditary.double,Hereditary.singleton]
  change (if cardHF (unionHF (Hereditary.pair x y)) = ordinal 1 then x else
    uniqueHF (ofFinset ((elements (unionHF (Hereditary.pair x y))).filter
      fun z => z ∉ elements (Hereditary.singleton x)))) = y
  rw [hu]
  by_cases h : x = y
  · rw [h]
    simp [cardHF,Hereditary.double]
  · rw [ite_eq_right (cardHF_double_ne x y h)]
    have hf : (elements (Hereditary.double x y)).filter
        (fun z => z ∉ elements (Hereditary.singleton x)) = {y} := by
      ext z
      simp [Hereditary.double,Hereditary.singleton]
      aesop
    rw [hf]
    exact uniqueHF_singleton y

end

variable {n : ℕ}

def tupleProduct : {n : ℕ} → (k : ℕ) → QuotedTerm n → QuotedTerm n
  | _, 0, _ => empty.singleton
  | _, k+1, r => r.bind ((tupleProduct k r.up).map ((var 1).pair (var 0)))

variable {A : Type} [Fintype A]

lemma mem_tupleProduct (k : ℕ) (r : QuotedTerm n) (S : Input A) (env : Fin n → HF A) (z : HF A) :
    z ∈ elements ((tupleProduct k r).meaning S env) ↔
      ∃ f : Fin k → HF A, (∀ i, f i ∈ elements (r.meaning S env)) ∧ tupleCode (List.ofFn f) = z := by
  induction k generalizing n z with
  | zero =>
    simp only [tupleProduct,meaning_singleton,meaning_empty,Hereditary.singleton,elements_ofFinset,
      Finset.mem_singleton,List.ofFn_zero,tupleCode]
    constructor
    · intro h; exact ⟨Fin.elim0,fun i => Fin.elim0 i,h.symm⟩
    · rintro ⟨f,hf,he⟩; exact he.symm
  | succ k ih =>
    simp only [tupleProduct,meaning_bind,meaning_map,meaning_pair,meaning_var,Fin.cons_zero,
      Fin.cons_one,elements_ofFinset,Finset.mem_biUnion,Finset.mem_image,ih,meaning_up]
    constructor
    · rintro ⟨a,ha,b,⟨f,hf,hb⟩,he⟩
      refine ⟨Fin.cons a f,?_,?_⟩
      · intro i; refine Fin.cases ha hf i
      · simp only [List.ofFn_succ,Fin.cons_zero,Fin.cons_succ,tupleCode]
        rw [hb,he]
    · rintro ⟨f,hf,he⟩
      refine ⟨f 0,hf 0,tupleCode (List.ofFn (fun i => f i.succ)),?_,?_⟩
      · exact ⟨fun i => f i.succ,fun i => hf i.succ,rfl⟩
      · simpa only [List.ofFn_succ,tupleCode] using he

def blockParameters : QuotedTerm n := tupleProduct 4 vertexBlocks

lemma mem_blockParameters (S : Input A) (env : Fin n → HF A) (z : HF A) :
    z ∈ elements ((blockParameters : QuotedTerm n).meaning S env) ↔
      ∃ α : Fin 4 → Finset A, (∀ i, α i ∈ WitnessedChoice.vertexBlocks S) ∧ parameterCode α = z := by
  rw [blockParameters,mem_tupleProduct]
  simp only [meaning_vertexBlocks,elements_ofFinset]
  constructor
  · rintro ⟨f,hf,hz⟩
    have h (i) := Finset.mem_image.mp (hf i)
    choose α hα hαf using h
    refine ⟨α,hα,?_⟩
    have he : stateCode ∘ α = f := funext hαf
    simpa only [parameterCode,he] using hz
  · rintro ⟨α,hα,hz⟩
    refine ⟨stateCode ∘ α,?_,hz⟩
    intro i
    exact Finset.mem_image.mpr ⟨α i,hα i,rfl⟩

end QuotedTerm

lemma collect_on {A : Type} (r : HF A) (guard : HF A → Result Bool) (body : HF A → Result (HF A))
    (g : HF A → Bool) (b : HF A → HF A)
    (hg : ∀ x ∈ elements r, guard x = some (g x))
    (hb : ∀ x ∈ elements r, g x = true → body x = some (b x)) :
    collect r guard body = some (ofFinset (((elements r).filter (fun x => g x = true)).image b)) := by
  have hgood : (∀ x ∈ elements r, (guard x).isSome) ∧
      (∀ x ∈ elements r, guard x = some true → (body x).isSome) := by
    constructor
    · intro x hx; rw [hg x hx]; simp
    · intro x hx ht
      rw [hg x hx] at ht
      rw [hb x hx (Option.some.inj ht)]
      simp
  rw [collect,ite_eq_left hgood]
  apply congrArg some
  apply ofFinset_inj.mpr
  have hf : (elements r).filter (fun x => guard x = some true) =
      (elements r).filter (fun x => g x = true) := Finset.filter_congr (by
        intro x hx
        rw [hg x hx,Option.some.injEq])
  rw [hf]
  apply Finset.image_congr
  intro x hx
  obtain ⟨hx,ht⟩ := Finset.mem_filter.mp hx
  change (body x).getD emptyHF = b x
  rw [hb x hx ht,Option.getD_some]

lemma Formula.eval_existsIn_on {A : Type} [Fintype A] (S : Input A) (p : Polynomial ℝ) {n : ℕ}
    (r : Term n) (a : Formula (n+1)) (env : Fin n → HF A)
    {rv : HF A} {av : HF A → Bool} (hr : r.eval S p env = some rv)
    (ha : ∀ x ∈ elements rv, a.eval S p (Fin.cons x env) = some (av x)) :
    (Formula.existsIn r a).eval S p env = some (decide (∃ x ∈ elements rv, av x = true)) := by
  simp only [Formula.existsIn,Formula.eval,Term.eval,hr,Option.bind_some]
  rw [collect_on rv _ _ av (fun _ => emptyHF) ha (by intros; rfl)]
  simp only [lift₂,Option.bind_some,Option.map_some,Option.some.injEq]
  have he : ofFinset (((elements rv).filter (fun x => av x = true)).image (fun _ => (emptyHF : HF A))) = emptyHF ↔
      ¬ ∃ x ∈ elements rv, av x = true := by
    rw [emptyHF,ofFinset_inj,Finset.image_eq_empty]
    simp
  simp only [he,decide_not,Bool.not_not]


namespace QuotedFormula

variable {n : ℕ}

def falsehood : QuotedFormula n := truth.neg

def anyList : List (QuotedFormula n) → QuotedFormula n
  | [] => falsehood
  | a::l => a.or (anyList l)

def allFin (k : ℕ) (f : Fin k → QuotedFormula n) : QuotedFormula n := allList (List.ofFn f)

def anyFin (k : ℕ) (f : Fin k → QuotedFormula n) : QuotedFormula n := anyList (List.ofFn f)

def nonempty (a : QuotedTerm n) : QuotedFormula n := (eq a .empty).neg

end QuotedFormula

namespace QuotedTerm

variable {n : ℕ}

def distanceAt (R u v : QuotedTerm n) : QuotedTerm n :=
  (indices.filter ((QuotedFormula.mem (triple u.up v.up (.var 0)) R.up).and
    (.allIn indices ((QuotedFormula.mem (.var 0) (.var 1)).imp
      ((QuotedFormula.mem (triple u.up.up v.up.up (.var 0)) R.up.up).neg))))).unique

end QuotedTerm

namespace QuotedFormula

open QuotedTerm

variable {n : ℕ}

def connected (R u v : QuotedTerm n) : QuotedFormula n :=
  mem (triple u v atoms.card) R

def resolving (α V R : QuotedTerm n) : QuotedFormula n :=
  allIn V (allIn V.up ((allFin 4 (fun i =>
    eq (distanceAt R.up.up ((α.up.up).component i.val) (.var 1))
      (distanceAt R.up.up ((α.up.up).component i.val) (.var 0)))).imp (eq (.var 1) (.var 0))))

def vertexLt (α R u v : QuotedTerm n) : QuotedFormula n :=
  anyFin 4 (fun i => (allFin 4 (fun j => if j.val < i.val then
    eq (distanceAt R (α.component j.val) u) (distanceAt R (α.component j.val) v)
    else truth)).and
      (mem (distanceAt R (α.component i.val) u) (distanceAt R (α.component i.val) v)))

def leastVertex (α V R v : QuotedTerm n) : QuotedFormula n :=
  (mem v V).and (allIn V ((vertexLt α.up R.up (.var 0) v.up).neg))

def hasEndpoints (e u v : QuotedTerm n) : QuotedFormula n :=
  (eq u v).neg.and ((incident u e).and (incident v e))

def edgeLt (α V R e f : QuotedTerm n) : QuotedFormula n :=
  existsIn V (existsIn V.up (existsIn V.up.up (existsIn V.up.up.up
    (allList [hasEndpoints e.up.up.up.up (.var 3) (.var 2),
      hasEndpoints f.up.up.up.up (.var 1) (.var 0),
      vertexLt α.up.up.up.up R.up.up.up.up (.var 3) (.var 2),
      vertexLt α.up.up.up.up R.up.up.up.up (.var 1) (.var 0),
      (vertexLt α.up.up.up.up R.up.up.up.up (.var 3) (.var 1)).or
        ((eq (.var 3) (.var 1)).and
          (vertexLt α.up.up.up.up R.up.up.up.up (.var 2) (.var 0)))]))))

def parentEligible (E R r v w : QuotedTerm n) : QuotedFormula n :=
  (adjacent E v w).and (eq (distanceAt R r w).successor (distanceAt R r v))

def parent (α V E R r v w : QuotedTerm n) : QuotedFormula n :=
  (parentEligible E R r v w).and
    (allIn V ((parentEligible E.up R.up r.up v.up (.var 0)).imp
      ((vertexLt α.up R.up (.var 0) w.up).neg)))

end QuotedFormula

namespace QuotedTerm

open QuotedFormula

variable {n : ℕ}

def root (α V R : QuotedTerm n) : QuotedTerm n :=
  (V.filter (leastVertex α.up V.up R.up (.var 0))).unique

def tree (α V E R : QuotedTerm n) : QuotedTerm n :=
  E.filter (existsIn V.up (existsIn V.up.up
    ((parent α.up.up.up V.up.up.up E.up.up.up R.up.up.up
      (root α V R).up.up.up (.var 1) (.var 0)).and
        (hasEndpoints (.var 2) (.var 1) (.var 0)))))

def nextEdges (α V E R T x : QuotedTerm n) : QuotedTerm n :=
  ((E.diff T).filter (eq (x.up.inter (.var 0)) .empty)).filter
    (allIn (E.diff T).up (((eq (x.up.up.inter (.var 0)) .empty).and
      (edgeLt α.up.up V.up.up R.up.up (.var 0) (.var 1))).neg))

end QuotedTerm

namespace SourceSyntax

open QuotedTerm QuotedFormula

variable {n : ℕ}

def next4 (i : Fin 4) : Fin 4 := ⟨(i.val+1)%4,Nat.mod_lt _ (by decide)⟩

def prev4 (i : Fin 4) : Fin 4 := ⟨(i.val+3)%4,Nat.mod_lt _ (by decide)⟩

def fv (f : QuotedTerm n) (i : Fin 4) : QuotedTerm n := f.fst.component i.val

def fe (f : QuotedTerm n) (i : Fin 4) : QuotedTerm n := f.snd.component i.val

def faceDescription (f : QuotedTerm n) : QuotedFormula n :=
  allFin 4 (fun i => (allFin 4 (fun j => if i=j then truth else
    ((eq (fv f i) (fv f j)).neg.and (eq (fe f i) (fe f j)).neg))).and
      (hasEndpoints (fe f i) (fv f i) (fv f (next4 i))))

def faces (V E : QuotedTerm n) : QuotedTerm n :=
  ((tupleProduct 4 V).bind ((tupleProduct 4 E.up).map ((var 1).pair (var 0)))).filter
    (faceDescription (.var 0))

def adjacentMatch (f s t : QuotedTerm n) (i j : Fin 4) : QuotedFormula n :=
  allList [mem s (fe f i),mem t (fe f j),
    existsIn (fv f (if j=next4 i then j else i))
      ((input .I (.var 0) s.up).and (input .I (.var 0) t.up))]

def matchFace (f s t : QuotedTerm n) : QuotedFormula n :=
  anyFin 4 (fun i => anyFin 4 (fun j =>
    (mem s (fe f i)).and ((mem t (fe f j)).and
      (if j=next4 i ∨ j=prev4 i then adjacentMatch f s t i j else
        existsIn (fe f (next4 i))
          ((adjacentMatch f.up s.up (.var 0) i (next4 i)).and
            (adjacentMatch f.up t.up (.var 0) j (next4 i)))))))

def side (f e : QuotedTerm n) : QuotedFormula n :=
  anyFin 4 (fun i => eq e (fe f i))

def onSide (f s : QuotedTerm n) : QuotedFormula n :=
  anyFin 4 (fun i => mem s (fe f i))

def baseEq (F e s t : QuotedTerm n) : QuotedFormula n :=
  allIn F ((side (.var 0) e.up).imp (matchFace (.var 0) s.up t.up))

def candidates (F N x : QuotedTerm n) : QuotedTerm n :=
  N.bind ((var 0).filter (allIn F.up.up ((side (.var 0) (.var 2)).imp
    (allIn x.up.up.up ((onSide (.var 1) (.var 0)).imp
      (matchFace (.var 1) (.var 2) (.var 0)))))))

end SourceSyntax


namespace CPTTerm

variable {n : ℕ} {A : Type} [Fintype A]

def comprehend (r : CPTTerm n) (body : CPTTerm (n+1)) (guard : CPTFormula (n+1)) : CPTTerm n :=
  ⟨.comprehend body.code r.code guard.code,by
    simp only [Term.wscCount,r.count,body.count,guard.count,Nat.add_zero]⟩

def map (r : CPTTerm n) (body : CPTTerm (n+1)) : CPTTerm n :=
  r.comprehend body (.quoted .truth)

def union (a : CPTTerm n) : CPTTerm n := ⟨.union a.code,a.count⟩

def bind (r : CPTTerm n) (body : CPTTerm (n+1)) : CPTTerm n := (r.map body).union

theorem value_comprehend (r : CPTTerm n) (body : CPTTerm (n+1)) (guard : CPTFormula (n+1))
    (S : Input A) (p : Polynomial ℝ) (env : Fin n → HF A) :
    (r.comprehend body guard).value S p env = ofFinset
      (((elements (r.value S p env)).filter fun x => guard.value S p (Fin.cons x env) = true).image
        fun x => body.value S p (Fin.cons x env)) := by
  apply value_eq
  exact Term.eval_comprehend S p r.code body.code guard.code env (r.eval_value S p env)
    (fun x => body.eval_value S p _) (fun x => guard.eval_value S p _)

@[simp] theorem value_map (r : CPTTerm n) (body : CPTTerm (n+1))
    (S : Input A) (p : Polynomial ℝ) (env : Fin n → HF A) :
    (r.map body).value S p env = ofFinset ((elements (r.value S p env)).image
      fun x => body.value S p (Fin.cons x env)) := by
  rw [map,value_comprehend]
  simp only [CPTFormula.value_quoted,QuotedFormula.truth,QuotedFormula.meaning_eq,
    decide_true,Finset.filter_true]

@[simp] theorem value_union (a : CPTTerm n) (S : Input A) (p : Polynomial ℝ) (env : Fin n → HF A) :
    a.union.value S p env = unionHF (a.value S p env) := by
  apply value_eq
  simp only [union,Term.eval,a.eval_value,Option.map_some]

@[simp] theorem value_bind (r : CPTTerm n) (body : CPTTerm (n+1))
    (S : Input A) (p : Polynomial ℝ) (env : Fin n → HF A) :
    (r.bind body).value S p env = ofFinset ((elements (r.value S p env)).biUnion
      fun x => elements (body.value S p (Fin.cons x env))) := by
  simp [bind,value_union,unionHF,Finset.image_biUnion]

end CPTTerm


section

open RelationPools

variable {A : Type} [Fintype A]

def decodeRelation (r : HF A) : Relation A :=
  Finset.univ.filter fun ab => pairCode ab ∈ elements r

@[simp] lemma decodeRelation_code (r : Relation A) : decodeRelation (relationCode r) = r := by
  ext ab
  simp [decodeRelation]

namespace QuotedTerm

variable {n : ℕ}

def normalizeRelation (r : QuotedTerm n) : QuotedTerm n :=
  relation (.link (.var 1) (.var 0) r.up.up)

def normalizeRelations (r : QuotedTerm n) : QuotedTerm n := r.map (normalizeRelation (.var 0))

def normalizeCandidates (r : QuotedTerm n) : QuotedTerm n :=
  atomFilter ((QuotedFormula.mem (.var 0) r.up).and (.input .Ed (.var 0) (.var 0)))

@[simp] lemma meaning_normalizeRelation (S : Input A) (env : Fin n → HF A) (r : QuotedTerm n) :
    (normalizeRelation r).meaning S env = relationCode (decodeRelation (r.meaning S env)) := by
  simp only [normalizeRelation,meaning_relation,QuotedFormula.meaning_link,meaning_var,
    meaning_up,Fin.cons_zero,Fin.cons_one,decodeRelation,pairCode]
  congr 1

@[simp] lemma meaning_normalizeRelations (S : Input A) (env : Fin n → HF A) (r : QuotedTerm n) :
    (normalizeRelations r).meaning S env = ofFinset
      (((elements (r.meaning S env)).image decodeRelation).image relationCode) := by
  simp [normalizeRelations,Finset.image_image,Function.comp_def]

@[simp] lemma meaning_normalizeCandidates (S : Input A) (env : Fin n → HF A) (r : QuotedTerm n) :
    (normalizeCandidates r).meaning S env = stateCode
      (decodeState (r.meaning S env) ∩ WitnessedChoice.edgeAtoms S) := by
  simp only [normalizeCandidates,meaning_atomFilter,QuotedFormula.meaning_and,
    QuotedFormula.meaning_mem,QuotedFormula.meaning_input,meaning_var,meaning_up,Fin.cons_zero,inputHF_atoms]
  congr 1
  ext a
  simp [decodeState,WitnessedChoice.edgeAtoms]

end QuotedTerm

namespace CPTTerm

variable {n : ℕ}

def normalizeCandidates (t : CPTTerm n) : CPTTerm n :=
  t.letIn (.quoted (QuotedTerm.normalizeCandidates (.var 0)))

def normalizeRelations (t : CPTTerm n) : CPTTerm n :=
  t.letIn (.quoted (QuotedTerm.normalizeRelations (.var 0)))

@[simp] lemma value_normalizeCandidates (t : CPTTerm n) (S : Input A) (p : Polynomial ℝ) (env : Fin n → HF A) :
    t.normalizeCandidates.value S p env = stateCode
      (decodeState (t.value S p env) ∩ WitnessedChoice.edgeAtoms S) := by
  simp [normalizeCandidates]

@[simp] lemma value_normalizeRelations (t : CPTTerm n) (S : Input A) (p : Polynomial ℝ) (env : Fin n → HF A) :
    t.normalizeRelations.value S p env = ofFinset
      (((elements (t.value S p env)).image decodeRelation).image relationCode) := by
  simp [normalizeRelations]

end CPTTerm

structure GuardedProgram where
  localBound : ℕ
  candidates : CPTTerm 2
  cycles : CPTTerm 2
  output : CPTFormula 2

namespace GuardedProgram

variable (G : GuardedProgram)

def witnesses : CPTTerm 2 := G.cycles.normalizeRelations.letIn
  (.quoted (QuotedTerm.witnessRelations G.localBound .truth (.var 1) (.var 0)))

def choice : CPTTerm 2 := G.candidates.normalizeCandidates.letIn
  (G.witnesses.up.letIn (.quoted (QuotedTerm.guardedChoice (.var 1) (.var 0))))

def step : QuotedTerm 3 := QuotedTerm.selectionStep (.var 1) (.var 0)

def witness : CPTTerm 3 := G.witnesses.rename ![0,2]

def formula : Formula 1 := .wsc step.code G.choice.code G.witness.code G.output.code

lemma count : G.formula.wscCount = 1 := by
  simp only [formula,Formula.wscCount,step.count,G.choice.count,G.witness.count,G.output.count]

variable (S : Input A) (p : Polynomial ℝ) (α : HF A)

def candidateSet (x : Finset A) : Finset A :=
  decodeState (G.candidates.value S p (Fin.cons (stateCode x) (Fin.cons α Fin.elim0))) ∩
    WitnessedChoice.edgeAtoms S

def cycleSet (x : Finset A) : Finset (Relation A) :=
  (elements (G.cycles.value S p (Fin.cons (stateCode x) (Fin.cons α Fin.elim0)))).image decodeRelation

def selection : Selection A := guardedSelection G.localBound S True
  (G.candidateSet S p α) (G.cycleSet S p α)

lemma candidates_eq (x : Finset A) : (G.selection S p α).candidates x = G.candidateSet S p α x := by
  simp [selection,guardedSelection]

lemma candidate_edge (x : Finset A) {a : A} (h : a ∈ (G.selection S p α).candidates x) :
    a ∈ WitnessedChoice.edgeAtoms S := by
  rw [G.candidates_eq] at h
  exact (Finset.mem_inter.mp h).2

lemma witnesses_value (x : Finset A) :
    G.witnesses.value S p (Fin.cons (stateCode x) (Fin.cons α Fin.elim0)) =
      ofFinset (((G.selection S p α).witnesses x).image permutationGraph) := by
  simp only [witnesses,CPTTerm.value_letIn,CPTTerm.value_normalizeRelations,CPTTerm.value_quoted]
  convert QuotedTerm.meaning_witnessRelations S
    (Fin.cons (ofFinset ((G.cycleSet S p α x).image relationCode))
      (Fin.cons (stateCode x) (Fin.cons α Fin.elim0)))
    G.localBound .truth (.var 1) (.var 0) x (G.cycleSet S p α x) rfl rfl using 1 <;>
    simp [cycleSet,selection,guardedSelection,QuotedFormula.truth,witnessPool]

lemma choice_value (x : Finset A) :
    G.choice.value S p (Fin.cons (stateCode x) (Fin.cons α Fin.elim0)) =
      ofFinset (((G.selection S p α).choices x).image choiceCode) := by
  simp only [choice,CPTTerm.value_letIn,CPTTerm.value_normalizeCandidates,CPTTerm.value_up,
    CPTTerm.value_quoted,G.witnesses_value]
  apply QuotedTerm.meaning_guardedChoice S _ (.var 1) (.var 0) (G.selection S p α) x
  · simp only [QuotedTerm.meaning_var,Fin.cons_one]
    rw [G.candidates_eq]
    rfl
  · rfl

lemma realizes : Realizes (G.selection S p α)
    (fun x y => step.code.eval S p (Fin.cons y (Fin.cons x (Fin.cons α Fin.elim0))))
    (fun x => G.choice.code.eval S p (Fin.cons x (Fin.cons α Fin.elim0)))
    (fun z x => G.witness.code.eval S p (Fin.cons x (Fin.cons z (Fin.cons α Fin.elim0)))) := by
  constructor
  · intro x
    rw [G.choice.eval_value,G.choice_value]
  · intro x c hc
    rw [step.correct]
    apply congrArg some
    apply QuotedTerm.meaning_selectionStep S _ (.var 1) (.var 0) x c rfl rfl
    intro a ha
    subst c
    exact G.candidate_edge S p α x (Selection.some_mem_choices.mp hc).1
  · intro z x
    rw [G.witness.eval_value]
    change some ((G.witnesses.rename ![0,2]).value S p _) = _
    rw [CPTTerm.value_rename]
    have he : (Fin.cons (stateCode x) (Fin.cons (stateCode z) (Fin.cons α Fin.elim0))) ∘ ![0,2] =
        Fin.cons (stateCode x) (Fin.cons α Fin.elim0) := by
      funext i; fin_cases i <;> rfl
    rw [he,G.witnesses_value]

theorem boolean (α₀ : Fin 4 → Finset A) (hα : ∀ i, α₀ i ∈ blocks S)
    (hp : Fintype.card A+2 ≤ resource p (Fintype.card A)) :
    ∃ b : Bool, G.formula.eval S p (Fin.cons (parameterCode α₀) Fin.elim0) = some b := by
  apply (G.realizes S p (parameterCode α₀)).boolean
    (guardedSelection_filtered G.localBound S True _ _ α₀ hα)
    (resource p (Fintype.card A)) hp
  intro x
  rw [G.output.eval_value]
  simp

end GuardedProgram

end


structure ClosedGuardedProgram where
  parameters : CPTTerm 0
  body : GuardedProgram

namespace ClosedGuardedProgram

variable (G : ClosedGuardedProgram)

def parameterTerm : CPTTerm 0 := G.parameters.letIn (.quoted
  (QuotedTerm.blockParameters.filter (.mem (.var 0) (.var 1))))

def formula : Formula 0 := Formula.existsIn G.parameterTerm.code G.body.formula

def sentence (p : Polynomial ℝ) : Sentence := ⟨G.formula,p⟩

lemma count : G.formula.wscCount = 1 := by
  simp only [formula,Formula.existsIn,Formula.wscCount,Term.wscCount,
    G.parameterTerm.count,G.body.count,Nat.zero_add,Nat.add_zero]

variable {A : Type} [Fintype A]

lemma parameter_mem (S : Input A) (p : Polynomial ℝ) {z : HF A}
    (hz : z ∈ elements (G.parameterTerm.value S p Fin.elim0)) :
    ∃ α : Fin 4 → Finset A, (∀ i, α i ∈ WitnessedChoice.vertexBlocks S) ∧ parameterCode α = z := by
  simp only [parameterTerm,CPTTerm.value_letIn,CPTTerm.value_quoted,
    QuotedTerm.meaning_filter,elements_ofFinset,Finset.mem_filter] at hz
  exact (QuotedTerm.mem_blockParameters S _ z).mp hz.1

theorem boolean (S : Input A) (p : Polynomial ℝ)
    (hp : Fintype.card A+2 ≤ resource p (Fintype.card A)) :
    ∃ b : Bool, G.formula.eval S p Fin.elim0 = some b := by
  let bv (z : HF A) := (G.body.formula.eval S p (Fin.cons z Fin.elim0)).getD false
  have he (z : HF A) (hz : z ∈ elements (G.parameterTerm.value S p Fin.elim0)) :
      G.body.formula.eval S p (Fin.cons z Fin.elim0) = some (bv z) := by
    obtain ⟨α,hα,rfl⟩ := G.parameter_mem S p hz
    obtain ⟨b,hb⟩ := G.body.boolean S p α
      (fun i => Finset.mem_union_right _ (hα i)) hp
    simp only [bv,hb,Option.getD_some]
  refine ⟨_,Formula.eval_existsIn_on S p _ _ _ (G.parameterTerm.eval_value S p _) he⟩

theorem boolean_all (p : Polynomial ℝ) (hp : ∀ n : ℕ, n+2 ≤ resource p n) :
    (G.sentence p).BooleanOnAllInputs := by
  intro S
  exact G.boolean S.input p (hp _)

end ClosedGuardedProgram


namespace SourceSyntax

open QuotedTerm QuotedFormula

variable {n : ℕ}

def connWithout (H h u v : QuotedTerm n) : QuotedFormula n :=
  existsIn H ((eq (var 0).fst h.up).and (connected (var 0).snd u.up v.up))

def traversal (V T H e u v : QuotedTerm n) : QuotedTerm n :=
  (triple e u v).singleton.cup (T.bind (V.up.bind
    ((V.up.up.filter (allList [hasEndpoints (var 2) (var 1) (var 0),
      (connWithout H.up.up.up (var 2) v.up.up.up u.up.up.up).neg,
      connWithout H.up.up.up (var 2) v.up.up.up (var 1),
      connWithout H.up.up.up (var 2) u.up.up.up (var 0)])).map
        (triple (var 2) (var 1) (var 0)))))

def traversalEdge (Γ h : QuotedTerm n) : QuotedFormula n :=
  existsIn Γ (eq (var 0).fst h.up)

def directedZ (R Γ o h s t : QuotedTerm n) : QuotedFormula n :=
  existsIn Γ ((eq (var 0).fst h.up).and
    (((mem (distanceAt R.up o.up (var 0).snd.fst)
      (distanceAt R.up o.up (var 0).snd.snd)).and (input (.Z 1) s.up t.up)).or
     ((mem (distanceAt R.up o.up (var 0).snd.fst)
      (distanceAt R.up o.up (var 0).snd.snd)).neg.and (input (.Z 2) s.up t.up))))

def cycleY (E F R Γ o : QuotedTerm n) : QuotedTerm n :=
  relation (existsIn E.up.up (allList [mem (var 2) (var 0),mem (var 1) (var 0),
    ((traversalEdge Γ.up.up.up (var 0)).neg.and (eq (var 2) (var 1))).or
      ((traversalEdge Γ.up.up.up (var 0)).and
        ((baseEq F.up.up.up (var 0) (var 2) (var 1)).and
          (directedZ R.up.up.up Γ.up.up.up o.up.up.up (var 0) (var 2) (var 1))))]))

def cycleX (V E cY : QuotedTerm n) : QuotedTerm n :=
  relation (existsIn V.up.up (allList [mem (var 2) (var 0),mem (var 1) (var 0),
    allIn E.up.up.up ((incident (var 1) (var 0)).imp
      (existsIn (var 0) (existsIn (var 1)
        (allList [input .I (var 5) (var 1),input .I (var 4) (var 0),
          link (var 1) (var 0) cY.up.up.up.up.up.up]))))]))

def cycleRelation (V E F R Γ o : QuotedTerm n) : QuotedTerm n :=
  (cycleY E F R Γ o).cup (cycleX V E (cycleY E F R Γ o))

def cycleRelations (V E F R T H N : QuotedTerm n) : QuotedTerm n :=
  identity.singleton.cup (N.bind (V.up.bind (V.up.up.bind
    ((V.up.up.up.filter (hasEndpoints (var 3) (var 2) (var 1))).map
      (cycleRelation V.up.up.up.up E.up.up.up.up F.up.up.up.up R.up.up.up.up
        (traversal V.up.up.up.up T.up.up.up.up H.up.up.up.up (var 3) (var 2) (var 1))
        (var 0))))))

def complete (E T x : QuotedTerm n) : QuotedFormula n :=
  allList [eq x (x.inter QuotedTerm.edgeAtoms),
    allIn (E.diff T) (eq (x.up.inter (var 0)).card (nat 1)),
    allIn T (eq (x.up.inter (var 0)) empty)]

def allowed (E T x v t : QuotedTerm n) : QuotedFormula n :=
  allIn (E.diff T) ((incident v.up (var 0)).imp
    (existsIn (x.up.inter (var 0)) (input .I t.up.up (var 0))))

def unsupported (V T S v t : QuotedTerm n) : QuotedFormula n :=
  existsIn T (existsIn V.up (allList [
    (eq (var 0) v.up.up).neg,incident v.up.up (var 1),incident (var 0) (var 1),
    (existsIn ((var 0).diff S.up.up)
      (existsIn (var 2) ((input .I t.up.up.up.up (var 0)).and
        (input .I (var 1) (var 0))))).neg]))

def deletedStep (V E T x S : QuotedTerm n) : QuotedTerm n :=
  S.cup (QuotedTerm.configAtoms.filter (existsIn V.up ((mem (var 1) (var 0)).and
    ((allowed E.up.up T.up.up x.up.up (var 0) (var 1)).neg.or
      (unsupported V.up.up T.up.up S.up.up (var 0) (var 1))))))

end SourceSyntax

namespace SourceProgram

open QuotedTerm QuotedFormula SourceSyntax

def distances {n : ℕ} : CPTTerm n := CPTTerm.distance (.quoted QuotedTerm.vertexBlocks) (.quoted QuotedTerm.edgeBlocks)

def parameters : CPTTerm 0 := distances.letIn (.quoted (blockParameters.filter
  (resolving (var 0) QuotedTerm.vertexBlocks (var 1))))

def candidates : CPTTerm 2 := distances.letIn (.quoted
  (SourceSyntax.candidates (faces QuotedTerm.vertexBlocks QuotedTerm.edgeBlocks)
    (nextEdges (var 2) QuotedTerm.vertexBlocks QuotedTerm.edgeBlocks (var 0)
      (tree (var 2) QuotedTerm.vertexBlocks QuotedTerm.edgeBlocks (var 0)) (var 1)) (var 1)))

def connTable {n : ℕ} (V T : QuotedTerm n) : CPTTerm n :=
  (CPTTerm.quoted T).map ((CPTTerm.distance (.quoted V.up)
    (.quoted (T.up.diff (var 0).singleton))).letIn (.quoted ((var 1).pair (var 0))))

def cycles : CPTTerm 2 := distances.letIn ((CPTTerm.quoted
  (tree (var 2) QuotedTerm.vertexBlocks QuotedTerm.edgeBlocks (var 0))).letIn
    ((connTable QuotedTerm.vertexBlocks (var 0)).letIn (.quoted
      (cycleRelations QuotedTerm.vertexBlocks QuotedTerm.edgeBlocks (faces QuotedTerm.vertexBlocks QuotedTerm.edgeBlocks) (var 2)
        (var 1) (var 0) (nextEdges (var 4) QuotedTerm.vertexBlocks QuotedTerm.edgeBlocks (var 2) (var 1) (var 3))))))

def output : CPTFormula 2 := CPTFormula.letIn distances
  (CPTFormula.letIn (.quoted (tree (var 2) QuotedTerm.vertexBlocks QuotedTerm.edgeBlocks (var 0)))
    (CPTFormula.letIn ((CPTTerm.quoted
      (deletedStep QuotedTerm.vertexBlocks QuotedTerm.edgeBlocks (var 1) (var 3) (var 0))).iterate)
      (.quoted ((complete QuotedTerm.edgeBlocks (var 1) (var 3)).and
        (allIn QuotedTerm.vertexBlocks (nonempty ((var 0).diff (var 1))))))))

def program : ClosedGuardedProgram :=
  { parameters := parameters
    body := { localBound := RelationPools.localBound
              candidates := candidates
              cycles := cycles
              output := output } }

theorem one_occurrence : program.formula.wscCount = 1 := program.count

theorem boolean_all (p : Polynomial ℝ) (hp : ∀ n : ℕ, n+2 ≤ resource p n) :
    (program.sentence p).BooleanOnAllInputs := program.boolean_all p hp

end SourceProgram


namespace QuotedTerm

variable {n : ℕ} {A : Type} [Fintype A]

theorem closure_bound (t : QuotedTerm n) (S : Input A) (env : Fin n → HF A)
    (K : ℕ) (hK : tracePotential 0 env ≤ K) :
    (closure (t.meaning S env)).card ≤ t.code.traceBound.eval K := by
  have h : t.meaning S env = (t.code.traced S 0 env).1 := by
    have hh := (t.correct S 0 env).symm.trans (t.code.eval_traced S 0 t.count env)
    simpa only [resource,Polynomial.eval_zero,Nat.floor_zero] using Option.some.inj hh
  rw [h]
  exact (Finset.card_le_card (t.code.traced_closure S 0 env)).trans (t.code.traced_card_le S 0 env K hK)

theorem TC_bound (t : QuotedTerm n) (S : Input A) (env : Fin n → HF A)
    (K : ℕ) (hK : tracePotential 0 env ≤ K) :
    (TC (t.meaning S env)).card ≤ t.code.traceBound.eval K := by
  apply (Finset.card_le_card (show TC (t.meaning S env) ⊆ closure (t.meaning S env) from ?_)).trans
    (t.closure_bound S env K hK)
  rw [closure_eq_insert_TC]
  exact Finset.subset_insert _ _

end QuotedTerm


end WitnessedChoice.BGS

end

end OAI
