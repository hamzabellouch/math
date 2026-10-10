import OAI.Probability.SATComputability.LowerBounds
import OAI.Probability.SATComputability.CertificateSearch
import OAI.MathematicalPhysics.RapidForcing.BoundsPrograms

namespace OAI

namespace FixedClauseThreshold.Computability

open RapidForcing.EffectiveArithmetic

def words {α : Type*} (alphabet : List α) : ℕ → List (List α)
  | 0 => [[]]
  | n + 1 => alphabet.flatMap fun a => (words alphabet n).map (a :: ·)

theorem mem_words {α : Type*} (alphabet : List α) (n : ℕ) (w : List α) :
    w ∈ words alphabet n ↔ w.length = n ∧ ∀ a ∈ w, a ∈ alphabet := by
  induction n generalizing w with
  | zero => cases w <;> simp [words]
  | succ n ih =>
    cases w with
    | nil => simp [words]
    | cons a w => simp [words, ih, and_assoc, and_left_comm]

theorem nodup_words {α : Type*} {alphabet : List α} (ha : alphabet.Nodup)
    (n : ℕ) : (words alphabet n).Nodup := by
  induction n with
  | zero => simp [words]
  | succ n ih =>
    apply List.nodup_flatMap.mpr
    refine ⟨fun a _ => ih.map (fun _ _ h => (List.cons.inj h).2), ?_⟩
    apply ha.imp
    intro a b hab w haw hbw
    obtain ⟨u, _, rfl⟩ := List.mem_map.mp haw
    obtain ⟨v, _, hv⟩ := List.mem_map.mp hbw
    exact hab (List.cons.inj hv).1.symm

theorem words_primrec {α : Type*} [Primcodable α] :
    Primrec₂ (@words α) := by
  have h := Primrec.nat_rec' (f := fun p : List α × ℕ => p.2)
    (g := fun _ => ([[]] : List (List α)))
    (h := fun p q => p.1.flatMap fun a => q.2.map (a :: ·))
    Primrec.snd (Primrec.const _) ?_
  · exact h.of_eq fun p => by
      induction p.2 <;> simp_all [words]
  · apply Primrec.list_flatMap (Primrec.fst.comp Primrec.fst)
    apply Primrec.list_map (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
    exact Primrec.list_cons.comp
      (Primrec.snd.comp Primrec.fst) Primrec.snd

private theorem length_of_enumeration {α β : Type*} [Fintype α]
    [DecidableEq β] (l : List β) (hl : l.Nodup) (f : α → β)
    (hf : Function.Injective f) (hm : ∀ b, b ∈ l ↔ ∃ a, f a = b) :
    l.length = Fintype.card α := by
  let g : α → ↥l.toFinset := fun a => ⟨f a, by simp [hm]⟩
  have hg : Function.Bijective g := by
    constructor
    · intro a b h
      exact hf (congrArg Subtype.val h)
    · intro b
      obtain ⟨a, ha⟩ := (hm b).mp (List.mem_toFinset.mp b.property)
      exact ⟨a, Subtype.ext ha⟩
  rw [← List.toFinset_card_of_nodup hl, ← Fintype.card_coe]
  exact (Fintype.card_congr (Equiv.ofBijective g hg)).symm

def clauseAlphabet : List (Option Bool) := [none, some false, some true]

def clauseWords (n k : ℕ) : List (List (Option Bool)) :=
  (words clauseAlphabet n).filter fun c => (c.filter Option.isSome).length = k

def encodeClause {n k : ℕ} (c : ProperClause n k) : List (Option Bool) :=
  List.ofFn c.val

theorem literal_count_ofFn {n : ℕ} (c : Fin n → Option Bool) :
    ((List.ofFn c).filter Option.isSome).length =
      (Finset.univ.filter fun i => (c i).isSome).card := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, Fin.card_filter_univ_succ]
    simp only [List.filter_cons]
    split <;> simp_all

theorem mem_clauseWords_iff (n k : ℕ) (w : List (Option Bool)) :
    w ∈ clauseWords n k ↔ ∃ c : ProperClause n k, encodeClause c = w := by
  simp only [clauseWords, List.mem_filter, decide_eq_true_eq, mem_words]
  constructor
  · rintro ⟨⟨hlen, _⟩, hc⟩
    let f : Fin n → Option Bool := fun i => w.get ⟨i.val, by omega⟩
    have hf : List.ofFn f = w := by
      subst n
      exact List.ofFn_get w
    have hp : (Finset.univ.filter fun i => (f i).isSome).card = k := by
      rw [← literal_count_ofFn, hf]
      exact hc
    exact ⟨⟨f, hp⟩, hf⟩
  · rintro ⟨c, rfl⟩
    refine ⟨⟨List.length_ofFn, ?_⟩, ?_⟩
    · intro a _
      cases a with
      | none => simp [clauseAlphabet]
      | some b => cases b <;> simp [clauseAlphabet]
    · simpa only [encodeClause, literal_count_ofFn] using c.property

theorem encodeClause_injective {n k : ℕ} :
    Function.Injective (@encodeClause n k) := by
  intro a b h
  apply Subtype.ext
  exact List.ofFn_injective h

def formulaWords (n k m : ℕ) : List (List (List (Option Bool))) :=
  words (clauseWords n k) m

def encodeFormula {n k m : ℕ} (f : Formula n k m) : List (List (Option Bool)) :=
  List.ofFn fun j => encodeClause (f j)

theorem encodeFormula_injective {n k m : ℕ} :
    Function.Injective (@encodeFormula n k m) := by
  intro a b h
  have he := List.ofFn_injective h
  funext j
  exact encodeClause_injective (congrFun he j)

theorem mem_formulaWords_iff (n k m : ℕ) (w : List (List (Option Bool))) :
    w ∈ formulaWords n k m ↔ ∃ f : Formula n k m, encodeFormula f = w := by
  rw [formulaWords, mem_words]
  constructor
  · rintro ⟨hlen, hw⟩
    have hget (i : Fin m) : ∃ c : ProperClause n k,
        encodeClause c = w.get ⟨i.val, by omega⟩ :=
      (mem_clauseWords_iff n k _).mp
        (hw _ (List.get_mem w ⟨i.val, by omega⟩))
    choose f hf using hget
    refine ⟨f, ?_⟩
    unfold encodeFormula
    simp_rw [hf]
    subst m
    exact List.ofFn_get w
  · rintro ⟨f, rfl⟩
    refine ⟨List.length_ofFn, ?_⟩
    intro c hc
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
    exact (mem_clauseWords_iff n k _).mpr ⟨f i, rfl⟩

theorem formulaWords_length (n k m : ℕ) :
    (formulaWords n k m).length = Fintype.card (Formula n k m) := by
  apply length_of_enumeration _ _ encodeFormula encodeFormula_injective
    (mem_formulaWords_iff n k m)
  exact nodup_words ((nodup_words (by decide : clauseAlphabet.Nodup) n).filter _) m

def clauseHolds (s : List Bool) (c : List (Option Bool)) : Prop :=
  ∃ i ∈ List.range s.length, c.getD i none = some (s.getD i false)

instance (s : List Bool) (c : List (Option Bool)) : Decidable (clauseHolds s c) := by
  unfold clauseHolds
  infer_instance

def formulaHolds (s : List Bool) (f : List (List (Option Bool))) : Prop :=
  ∀ c ∈ f, clauseHolds s c

instance (s : List Bool) (f : List (List (Option Bool))) : Decidable (formulaHolds s f) := by
  unfold formulaHolds
  infer_instance

def formulaSatisfiable (n : ℕ) (f : List (List (Option Bool))) : Prop :=
  ∃ s ∈ words [false, true] n, formulaHolds s f

instance (n : ℕ) (f : List (List (Option Bool))) : Decidable (formulaSatisfiable n f) := by
  unfold formulaSatisfiable
  infer_instance

theorem clauseHolds_ofFn {n k : ℕ} (s : Assignment n) (c : ProperClause n k) :
    clauseHolds (List.ofFn s) (encodeClause c) ↔ SatisfiesClause s c := by
  simp only [clauseHolds, List.length_ofFn, List.mem_range, SatisfiesClause]
  constructor
  · rintro ⟨i, hi, h⟩
    exact ⟨⟨i, hi⟩, by simpa [encodeClause, List.getD, hi] using h⟩
  · rintro ⟨i, hi⟩
    exact ⟨i.val, i.isLt, by simpa [encodeClause, List.getD, i.isLt] using hi⟩

theorem formulaHolds_ofFn {n k m : ℕ} (s : Assignment n) (f : Formula n k m) :
    formulaHolds (List.ofFn s) (encodeFormula f) ↔ Satisfies s f := by
  constructor
  · intro h j
    exact (clauseHolds_ofFn s (f j)).mp (h _ (List.mem_ofFn.mpr ⟨j, rfl⟩))
  · intro h c hc
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hc
    exact (clauseHolds_ofFn s (f j)).mpr (h j)

theorem formulaSatisfiable_encode {n k m : ℕ} (f : Formula n k m) :
    formulaSatisfiable n (encodeFormula f) ↔ Satisfiable f := by
  constructor
  · rintro ⟨s, hs, hf⟩
    obtain ⟨hlen, _⟩ := (mem_words _ _ _).mp hs
    let a : Assignment n := fun i => s.get ⟨i.val, by omega⟩
    have ha : List.ofFn a = s := by subst n; exact List.ofFn_get s
    exact ⟨a, (formulaHolds_ofFn a f).mp (ha ▸ hf)⟩
  · rintro ⟨s, hs⟩
    refine ⟨List.ofFn s, (mem_words _ _ _).mpr ⟨List.length_ofFn, ?_⟩,
      (formulaHolds_ofFn s f).mpr hs⟩
    intro b _
    cases b <;> simp

def satisfiableWords (n k m : ℕ) : List (List (List (Option Bool))) :=
  (formulaWords n k m).filter (formulaSatisfiable n)

theorem satisfiableWords_length (n k m : ℕ) :
    (satisfiableWords n k m).length =
      Fintype.card {f : Formula n k m // Satisfiable f} := by
  refine length_of_enumeration _ ?_ (fun f => encodeFormula f.val) ?_ ?_
  · exact ((nodup_words ((nodup_words (by decide : clauseAlphabet.Nodup) n).filter _) m).filter _)
  · intro a b h
    exact Subtype.ext (encodeFormula_injective h)
  · intro w
    simp only [satisfiableWords, List.mem_filter, decide_eq_true_eq, mem_formulaWords_iff]
    constructor
    · rintro ⟨⟨f, rfl⟩, hf⟩
      exact ⟨⟨f, formulaSatisfiable_encode f |>.mp hf⟩, rfl⟩
    · rintro ⟨⟨f, hf⟩, rfl⟩
      exact ⟨⟨f, rfl⟩, (formulaSatisfiable_encode f).mpr hf⟩

def enumeratedProbability (n k m : ℕ) : ℚ :=
  (satisfiableWords n k m).length / (formulaWords n k m).length

theorem enumeratedProbability_eq (n k m : ℕ) :
    enumeratedProbability n k m = rationalProbability n k m := by
  simp only [enumeratedProbability, satisfiableWords_length, formulaWords_length,
    rationalProbability]

theorem clauseWords_primrec : Primrec₂ clauseWords := by
  have hi : PrimrecPred (fun c : Option Bool => c.isSome) :=
    Primrec.eq.comp Primrec.option_isSome (Primrec.const true)
  have hc : Primrec (fun c : List (Option Bool) => (c.filter Option.isSome).length) := by
    simpa only [decide_eq_true_eq, Bool.decide_coe] using
      Primrec.list_length.comp (Primrec.listFilter hi)
  have hp : PrimrecRel (fun c : List (Option Bool) => fun k : ℕ =>
      (c.filter Option.isSome).length = k) :=
    Primrec.eq.comp (hc.comp Primrec.fst) Primrec.snd
  exact hp.listFilter.comp
    (words_primrec.comp (Primrec.const clauseAlphabet) Primrec.fst) Primrec.snd

theorem formulaWords_primrec : Primrec (fun p : ℕ × ℕ × ℕ =>
    formulaWords p.1 p.2.1 p.2.2) := by
  exact words_primrec.comp
    (clauseWords_primrec.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
    (Primrec.snd.comp Primrec.snd)

theorem clauseHolds_primrec : PrimrecRel clauseHolds := by
  have hbase : PrimrecRel (fun i : ℕ => fun p : List Bool × List (Option Bool) =>
      p.2.getD i none = some (p.1.getD i false)) :=
    Primrec.eq.comp
      ((Primrec.list_getD none).comp (Primrec.snd.comp Primrec.snd) Primrec.fst)
      (Primrec.option_some.comp
        ((Primrec.list_getD false).comp (Primrec.fst.comp Primrec.snd) Primrec.fst))
  exact hbase.exists_mem_list.comp
    (Primrec.list_range.comp (Primrec.list_length.comp Primrec.fst)) Primrec.id

theorem formulaHolds_primrec : PrimrecRel formulaHolds := by
  have hc : PrimrecRel (fun c : List (Option Bool) => fun s : List Bool =>
      clauseHolds s c) := clauseHolds_primrec.comp Primrec.snd Primrec.fst
  exact hc.forall_mem_list.comp Primrec.snd Primrec.fst

theorem formulaSatisfiable_primrec : PrimrecRel formulaSatisfiable := by
  exact formulaHolds_primrec.exists_mem_list.comp
    (words_primrec.comp (Primrec.const [false, true]) Primrec.fst) Primrec.snd

theorem satisfiableWords_primrec : Primrec (fun p : ℕ × ℕ × ℕ =>
    satisfiableWords p.1 p.2.1 p.2.2) := by
  have hs : PrimrecRel (fun f : List (List (Option Bool)) => fun n : ℕ =>
      formulaSatisfiable n f) := formulaSatisfiable_primrec.comp Primrec.snd Primrec.fst
  exact hs.listFilter.comp formulaWords_primrec Primrec.fst

@[fun_prop] theorem rationalProbability_computable :
    Computable (fun p : ℕ × ℕ × ℕ => rationalProbability p.1 p.2.1 p.2.2) := by
  have hn := (Primrec.list_length.comp satisfiableWords_primrec).to_comp
  have hd := (Primrec.list_length.comp formulaWords_primrec).to_comp
  have he : Computable (fun p : ℕ × ℕ × ℕ => enumeratedProbability p.1 p.2.1 p.2.2) := by
    unfold enumeratedProbability
    fun_prop
  exact he.of_eq (fun p => enumeratedProbability_eq p.1 p.2.1 p.2.2)

attribute [local irreducible] rationalProbability

private theorem probabilities_map_computable :
    Computable₂ (fun p : ℕ × ℕ => fun j : ℕ =>
      rationalProbability p.1 p.2 (j + 1)) := by
  have hi : Computable (fun p : (ℕ × ℕ) × ℕ => (p.1.1, p.1.2, p.2 + 1)) := by
    fun_prop
  change Computable (fun p : (ℕ × ℕ) × ℕ =>
    (fun q : ℕ × ℕ × ℕ => rationalProbability q.1 q.2.1 q.2.2)
      (p.1.1, p.1.2, p.2 + 1))
  exact Computable.comp rationalProbability_computable hi

private theorem cap_computable : Computable (fun p : ℕ × ℕ => mainCap p.1 p.2) := by
  unfold mainCap capMultiplier
  fun_prop

@[fun_prop] theorem rationalCenter_computable :
    Computable (fun p : ℕ × ℕ => rationalCenter p.1 p.2) := by
  have hs : Computable (fun p : ℕ × ℕ =>
      ((List.range (mainCap p.1 p.2)).map fun j =>
        rationalProbability p.1 p.2 (j + 1)).sum) := by
    apply (computable_list_sum computable_rat_add).comp
    apply computable_list_map
    · exact Primrec.list_range.to_comp.comp cap_computable
    · exact probabilities_map_computable
  have he : Computable (fun p : ℕ × ℕ =>
      ((List.range (mainCap p.1 p.2)).map fun j =>
        rationalProbability p.1 p.2 (j + 1)).sum / p.1) := by fun_prop
  apply he.of_eq
  intro p
  have hl (N : ℕ) :
      ((List.range N).map fun j => rationalProbability p.1 p.2 (j + 1)).sum =
        ∑ j ∈ Finset.range N, rationalProbability p.1 p.2 (j + 1) := by
    induction N with
    | zero => simp
    | succ N ih => simp [List.range_succ, Finset.sum_range_succ, ih]
  change _ = rationalCenter p.1 p.2
  unfold rationalCenter
  rw [hl]

end FixedClauseThreshold.Computability

end OAI
