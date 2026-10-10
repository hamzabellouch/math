import Mathlib
import OAI.Computability.DirectedFeedback.Encoding.InstanceEquivalences

namespace OAI


namespace DFVSGames.Foundations.Complexity

open Target

def parseLiteral («variables» : Nat) : List Nat → Option (Literal «variables» × List Nat)
  | index :: sign :: rest =>
      if bounded : index < «variables» then
        if sign = 0 then some (⟨⟨index, bounded⟩, false⟩, rest)
        else if sign = 1 then some (⟨⟨index, bounded⟩, true⟩, rest)
        else none
      else none
  | _ => none

@[simp] theorem parseLiteral_encoded {n : Nat} (literal : Literal n) (rest : List Nat) :
    parseLiteral n (literalWords literal ++ rest) = some (literal, rest) := by
  cases literal with
  | mk index positive =>
      cases positive <;> simp [literalWords, parseLiteral, index.isLt]

def parseClause («variables» : Nat) (words : List Nat) : Option (Clause «variables» × List Nat) := do
  let (a, words) ← parseLiteral «variables» words
  let (b, words) ← parseLiteral «variables» words
  let (c, words) ← parseLiteral «variables» words
  return (⟨#[a, b, c], rfl⟩, words)

theorem clause_three_entries {n : Nat} (clause : Clause n) :
    (⟨#[clause[0], clause[1], clause[2]], rfl⟩ : Clause n) = clause := by
  apply Vector.ext
  intro i hi
  have cases_i : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases cases_i with rfl | rfl | rfl <;> rfl

@[simp] theorem parseClause_encoded {n : Nat} (clause : Clause n) (rest : List Nat) :
    parseClause n (clauseWords clause ++ rest) = some (clause, rest) := by
  simp [clauseWords, List.append_assoc, parseClause, parseLiteral_encoded,
    clause_three_entries]

def parseClauses («variables» : Nat) : Nat → List Nat → Option (List (Clause «variables») × List Nat)
  | 0, words => some ([], words)
  | count + 1, words => do
      let (clause, words) ← parseClause «variables» words
      let (clauses, words) ← parseClauses «variables» count words
      return (clause :: clauses, words)

@[simp] theorem parseClauses_encoded {n : Nat} (clauses : List (Clause n)) (rest : List Nat) :
    parseClauses n clauses.length (clauses.flatMap clauseWords ++ rest) = some (clauses, rest) := by
  induction clauses with
  | nil => rfl
  | cons clause clauses ih =>
      simp [List.append_assoc, parseClauses, parseClause_encoded, ih]

def decodeFormulaWords : List Nat → Option Formula
  | «variables» :: count :: words => do
      let (clauses, trailing) ← parseClauses «variables» count words
      if trailing = [] then some ⟨«variables», clauses⟩ else none
  | _ => none

@[simp] theorem decodeFormulaWords_encoded (formula : Formula) :
    decodeFormulaWords (formulaWords formula) = some formula := by
  cases formula with
  | mk «variables» clauses =>
      have parsed := parseClauses_encoded clauses []
      simp only [List.append_nil] at parsed
      simp [decodeFormulaWords, formulaWords, parsed]

def decodeFormulaBits (bits : List Bool) : Option Formula :=
  decodeWords bits >>= decodeFormulaWords

@[simp] theorem decodeFormulaBits_encoded (formula : Formula) :
    decodeFormulaBits (formulaBits formula) = some formula := by
  simp [decodeFormulaBits, formulaBits]

theorem formulaBits_injective {first second : Formula}
    (same : formulaBits first = formulaBits second) : first = second := by
  have parsed := congrArg decodeFormulaBits same
  simpa only [decodeFormulaBits_encoded, Option.some.injEq] using parsed

end DFVSGames.Foundations.Complexity


namespace DFVSGames.Foundations.Complexity

open Target

def parseLabel (alphabet value : Nat) : Option (Fin alphabet) :=
  if bounded : value < alphabet then some ⟨value, bounded⟩ else none

@[simp] theorem parseLabel_value {q : Nat} (label : Fin q) :
    parseLabel q label.val = some label := by simp [parseLabel, label.isLt]

@[simp] theorem parseLabels_values {q : Nat} (labels : List (Fin q)) :
    (labels.map Fin.val).mapM (parseLabel q) = some labels := by
  induction labels with
  | nil => rfl
  | cons label labels ih => simp [ih]

def parseImages (alphabet : Nat) (words : List Nat) : Option (Vector (Fin alphabet) alphabet) := do
  let labels ← words.mapM (parseLabel alphabet)
  if length_ok : labels.length = alphabet then
    some ⟨labels.toArray, by simpa using length_ok⟩
  else none

@[simp] theorem parseImages_values {q : Nat} (images : Vector (Fin q) q) :
    parseImages q (images.toList.map Fin.val) = some images := by
  unfold parseImages
  rw [parseLabels_values]
  simp
  exact Vector.toArray_toList

def findPreimage {q : Nat} (images : Vector (Fin q) q) (label : Fin q) : Fin q :=
  ((List.finRange q).find? (fun x => decide (images[x] = label))).getD label

theorem findPreimage_permutation {q : Nat} (table : PermutationTable q) (label : Fin q) :
    findPreimage table.images label = table.inverseImages[label] := by
  have exists_preimage :
      ((List.finRange q).find? (fun x => decide (table.images[x] = label))).isSome := by
    apply List.find?_isSome.mpr
    exact ⟨table.inverseImages[label], List.mem_finRange _, by
      simpa only [decide_eq_true_eq] using table.rightInverse label⟩
  cases found : (List.finRange q).find? (fun x => decide (table.images[x] = label)) with
  | none =>
      rw [found] at exists_preimage
      contradiction
  | some x =>
      have image_eq : table.images[x] = label := by
        simpa using List.find?_some found
      have x_eq := table.images_injective (image_eq.trans (table.rightInverse label).symm)
      unfold findPreimage
      rw [found]
      exact x_eq

def searchedInverse {q : Nat} (images : Vector (Fin q) q) : Vector (Fin q) q :=
  Vector.ofFn (findPreimage images)

theorem searchedInverse_permutation {q : Nat} (table : PermutationTable q) :
    searchedInverse table.images = table.inverseImages := by
  apply Vector.ext
  intro i hi
  simpa [searchedInverse] using findPreimage_permutation table ⟨i, hi⟩

def tableWords {q : Nat} (table : PermutationTable q) : List Nat :=
  table.images.toList.map Fin.val

def parsePermutation (alphabet : Nat) (words : List Nat) : Option (PermutationTable alphabet) := do
  let images ← parseImages alphabet words
  let inverseImages := searchedInverse images
  if left : ∀ label : Fin alphabet, inverseImages[images[label]] = label then
    if right : ∀ label : Fin alphabet, images[inverseImages[label]] = label then
      some ⟨images, inverseImages, left, right⟩
    else none
  else none

@[simp] theorem parsePermutation_encoded {q : Nat} (table : PermutationTable q) :
    parsePermutation q (tableWords table) = some table := by
  simp only [parsePermutation, tableWords, parseImages_values]
  dsimp only [Bind.bind, Option.bind]
  simp only [searchedInverse_permutation]
  simp only [table.leftInverse, table.rightInverse, implies_true, dite_true]

@[simp] theorem tableWords_length {q : Nat} (table : PermutationTable q) :
    (tableWords table).length = q := by simp [tableWords]

def constraintWords {n q : Nat} (constraint : Constraint n q) : List Nat :=
  [constraint.source.val, constraint.target.val] ++ tableWords constraint.permutation

def parseConstraint (vertices alphabet : Nat) :
    List Nat → Option (Constraint vertices alphabet × List Nat)
  | source :: target :: words => do
      let source ← parseLabel vertices source
      let target ← parseLabel vertices target
      let permutation ← parsePermutation alphabet (words.take alphabet)
      return (⟨source, target, permutation⟩, words.drop alphabet)
  | _ => none

@[simp] theorem parseConstraint_encoded {n q : Nat}
    (constraint : Constraint n q) (rest : List Nat) :
    parseConstraint n q (constraintWords constraint ++ rest) = some (constraint, rest) := by
  cases constraint with
  | mk source target permutation =>
      have taken := List.take_left' (l₂ := rest) (tableWords_length permutation)
      have dropped := List.drop_left' (l₂ := rest) (tableWords_length permutation)
      simp [constraintWords, parseConstraint, taken, dropped]

def parseConstraints (vertices alphabet : Nat) :
    Nat → List Nat → Option (List (Constraint vertices alphabet) × List Nat)
  | 0, words => some ([], words)
  | count + 1, words => do
      let (constraint, words) ← parseConstraint vertices alphabet words
      let (constraints, words) ← parseConstraints vertices alphabet count words
      return (constraint :: constraints, words)

@[simp] theorem parseConstraints_encoded {n q : Nat}
    (constraints : List (Constraint n q)) (rest : List Nat) :
    parseConstraints n q constraints.length (constraints.flatMap constraintWords ++ rest) =
      some (constraints, rest) := by
  induction constraints with
  | nil => rfl
  | cons constraint constraints ih =>
      simp [parseConstraints, List.append_assoc, ih]

def gameWords {q : Nat} (game : Instance q) : List Nat :=
  [game.vertices, q, game.constraints.length] ++ game.constraints.flatMap constraintWords

def gameBits {q : Nat} (game : Instance q) : List Bool := encodeWords (gameWords game)

def decodeGameWords (alphabet : Nat) : List Nat → Option (Instance alphabet)
  | vertices :: encodedAlphabet :: count :: words => do
      if encodedAlphabet = alphabet then
        let (constraints, trailing) ← parseConstraints vertices alphabet count words
        if trailing = [] then
          if nonempty : constraints ≠ [] then some ⟨vertices, constraints, nonempty⟩ else none
        else none
      else none
  | _ => none

@[simp] theorem decodeGameWords_encoded {q : Nat} (game : Instance q) :
    decodeGameWords q (gameWords game) = some game := by
  cases game with
  | mk vertices constraints nonempty =>
      have parsed := parseConstraints_encoded constraints []
      simp only [List.append_nil] at parsed
      simp [decodeGameWords, gameWords, parsed, nonempty]

def decodeGameBits (alphabet : Nat) (bits : List Bool) : Option (Instance alphabet) :=
  decodeWords bits >>= decodeGameWords alphabet

@[simp] theorem decodeGameBits_encoded {q : Nat} (game : Instance q) :
    decodeGameBits q (gameBits game) = some game := by
  simp [decodeGameBits, gameBits]

theorem gameBits_injective {q : Nat} {first second : Instance q}
    (same : gameBits first = gameBits second) : first = second := by
  have parsed := congrArg (decodeGameBits q) same
  simpa only [decodeGameBits_encoded, Option.some.injEq] using parsed

@[simp] theorem constraintWords_length {n q : Nat} (constraint : Constraint n q) :
    (constraintWords constraint).length = q + 2 := by simp [constraintWords]

theorem constraintsWords_length {n q : Nat} (constraints : List (Constraint n q)) :
    (constraints.flatMap constraintWords).length = constraints.length * (q + 2) := by
  induction constraints with
  | nil => simp
  | cons constraint constraints ih =>
      simp only [List.flatMap_cons, List.length_append, constraintWords_length,
        List.length_cons, Nat.add_mul, Nat.one_mul, ih]
      omega

@[simp] theorem gameWords_length {q : Nat} (game : Instance q) :
    (gameWords game).length = 3 + game.constraints.length * (q + 2) := by
  simp only [gameWords, List.length_append, List.length_cons, List.length_nil,
    constraintsWords_length]

end DFVSGames.Foundations.Complexity


namespace DFVSGames.Foundations.Complexity

def naturalWordsEncoding : Computability.Encoding (List Nat) Bool where
  encode := encodeWords
  decode := decodeWords
  decode_encode := decodeWords_encodeWords

def formulaEncoding : Computability.Encoding Target.Formula Bool where
  encode := formulaBits
  decode := decodeFormulaBits
  decode_encode := decodeFormulaBits_encoded

def gameEncoding (alphabet : Nat) : Computability.Encoding (Target.Instance alphabet) Bool where
  encode := gameBits
  decode := decodeGameBits alphabet
  decode_encode := decodeGameBits_encoded

def prefixBitMachine (bit : Bool) : Turing.FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := Unit
  initialState := ()
  m _ := .push () (fun _ => bit) .halt

noncomputable def prefixBitPolyTime (bit : Bool) :
    Turing.TM2ComputableInPolyTime (id : List Bool → List Bool) id (bit :: ·) where
  tm := prefixBitMachine bit
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 1
  outputsFun bs := {
    steps := 1
    evals_in_steps := by
      change some (Turing.TM2.stepAux (.push () (fun _ => bit) .halt) ()
          (fun _ : Unit => bs.map id)) =
        some { l := none, var := (), stk := fun _ : Unit => (bit :: bs).map id }
      simp [Turing.TM2.stepAux]
      funext k
      cases k
      rfl
    steps_le_m := by simp
  }

def enlargePolynomialBound {α β αΓ βΓ : Type}
    {ea : α → List αΓ} {eb : β → List βΓ} {f : α → β}
    (certificate : Turing.TM2ComputableInPolyTime ea eb f)
    (bound : Polynomial Nat)
    (larger : ∀ n, certificate.time.eval n ≤ bound.eval n) :
    Turing.TM2ComputableInPolyTime ea eb f where
  toTM2ComputableAux := certificate.toTM2ComputableAux
  time := bound
  outputsFun a := {
    toEvalsTo := (certificate.outputsFun a).toEvalsTo
    steps_le_m := Nat.le_trans (certificate.outputsFun a).steps_le_m (larger _)
  }

def composeMachinePhases {σ : Type} (step : σ → Option σ)
    (start intermediate : σ) (finish : Option σ)
    (p q : Polynomial Nat) (inputLength : Nat)
    (first : StateTransition.EvalsToInTime step start (some intermediate) (p.eval inputLength))
    (second : StateTransition.EvalsToInTime step intermediate finish (q.eval inputLength)) :
    StateTransition.EvalsToInTime step start finish ((p + q).eval inputLength) := by
  have composed := StateTransition.EvalsToInTime.trans step (p.eval inputLength)
    (q.eval inputLength) start intermediate finish first second
  simpa only [Polynomial.eval_add, Nat.add_comm] using composed

open Target

structure PolynomialGapReduction
    (completenessError soundnessError : RationalError)
    extends SemanticGapReduction completenessError soundnessError where
  computation : Turing.TM2ComputableInPolyTime formulaEncoding.encode
    (gameEncoding alphabet).encode reduce

end DFVSGames.Foundations.Complexity


namespace DFVSGames.Integration.RealTarget

open DFVSGames.Foundations
open Target

structure PolynomialGapReduction (ε δ : ℝ) where
  alphabet : Nat
  alphabetAtLeastTwo : 2 ≤ alphabet
  reduce : Formula → Instance alphabet
  computation : Turing.TM2ComputableInPolyTime Complexity.formulaEncoding.encode
    (Complexity.gameEncoding alphabet).encode reduce
  completeness : ∀ formula : Formula, formula.Satisfiable →
    ∃ labeling, 1 - ε ≤
      (countSatisfied labeling (reduce formula).constraints : ℝ) /
        (reduce formula).constraints.length
  soundness : ∀ formula : Formula, ¬ formula.Satisfiable →
    ∀ labeling, (countSatisfied labeling (reduce formula).constraints : ℝ) /
      (reduce formula).constraints.length ≤ δ

def ofRational {e d : RationalError} {ε δ : ℝ}
    (p : Complexity.PolynomialGapReduction e d)
    (hε : (GapSemantics.errorValue e : ℝ) ≤ ε)
    (hδ : (GapSemantics.errorValue d : ℝ) ≤ δ) : PolynomialGapReduction ε δ where
  alphabet := p.alphabet
  alphabetAtLeastTwo := p.alphabetAtLeastTwo
  reduce := p.reduce
  computation := p.computation
  completeness formula hformula := by
    obtain ⟨labeling, hlabel⟩ :=
      (GapSemantics.completeAt_iff_real e (p.reduce formula)).mp
        (p.completeness formula hformula)
    exact ⟨labeling, (sub_le_sub_left hε 1).trans hlabel⟩
  soundness formula hformula labeling :=
    ((GapSemantics.soundAt_iff_real d (p.reduce formula)).mp
      (p.soundness formula hformula) labeling).trans hδ

theorem for_all_real_of_dyadic
    (certificates : ∀ m n : Nat, Nonempty
      (Complexity.PolynomialGapReduction
        (DyadicErrors.dyadicError m) (DyadicErrors.dyadicError n)))
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    Nonempty (PolynomialGapReduction ε δ) := by
  obtain ⟨m, hm⟩ := DyadicErrors.exists_dyadic_below_real hε
  obtain ⟨n, hn⟩ := DyadicErrors.exists_dyadic_below_real hδ
  obtain ⟨p⟩ := certificates m n
  exact ⟨ofRational p hm.le hn.le⟩

end DFVSGames.Integration.RealTarget


namespace DFVSGames.Integration.InstanceValue

open DFVSGames.Foundations
open Target

def maxSatisfied {q : Nat} (g : Instance q) : Nat :=
  Finset.univ.sup (fun labeling : Fin g.vertices → Fin q =>
    countSatisfied labeling g.constraints)

noncomputable def value {q : Nat} (g : Instance q) : ℝ :=
  (maxSatisfied g : ℝ) / g.constraints.length

theorem countSatisfied_le_maxSatisfied {q : Nat} (g : Instance q)
    (labeling : Fin g.vertices → Fin q) :
    countSatisfied labeling g.constraints ≤ maxSatisfied g := by
  unfold maxSatisfied
  exact Finset.le_sup
    (f := fun labeling : Fin g.vertices → Fin q => countSatisfied labeling g.constraints)
    (Finset.mem_univ labeling)

theorem maxSatisfied_le_length {q : Nat} (g : Instance q) :
    maxSatisfied g ≤ g.constraints.length := by
  apply Finset.sup_le
  intro labeling _
  exact countSatisfied_le_length labeling g.constraints

theorem maxSatisfied_attained {q : Nat} (g : Instance q) (hq : 0 < q) :
    ∃ labeling : Fin g.vertices → Fin q,
      countSatisfied labeling g.constraints = maxSatisfied g := by
  have inhabited : (Finset.univ : Finset (Fin g.vertices → Fin q)).Nonempty :=
    ⟨fun _ => ⟨0, hq⟩, Finset.mem_univ _⟩
  obtain ⟨labeling, _, hmax⟩ := Finset.exists_mem_eq_sup Finset.univ inhabited
    (fun labeling : Fin g.vertices → Fin q => countSatisfied labeling g.constraints)
  exact ⟨labeling, hmax.symm⟩

theorem value_attained {q : Nat} (g : Instance q) (hq : 0 < q) :
    ∃ labeling : Fin g.vertices → Fin q,
      (countSatisfied labeling g.constraints : ℝ) / g.constraints.length = value g := by
  obtain ⟨labeling, hlabeling⟩ := maxSatisfied_attained g hq
  exact ⟨labeling, by rw [hlabeling]; rfl⟩

theorem labeling_rate_le_value {q : Nat} (g : Instance q)
    (labeling : Fin g.vertices → Fin q) :
    (countSatisfied labeling g.constraints : ℝ) / g.constraints.length ≤ value g := by
  apply div_le_div_of_nonneg_right
  · exact_mod_cast countSatisfied_le_maxSatisfied g labeling
  · exact Nat.cast_nonneg _

theorem satisfactionRate_le_value {q : Nat} (g : Instance q)
    (labeling : Fin g.vertices → Fin q) :
    (GapSemantics.satisfactionRate g labeling : ℝ) ≤ value g := by
  simpa [GapSemantics.satisfactionRate] using labeling_rate_le_value g labeling

theorem value_nonneg {q : Nat} (g : Instance q) : 0 ≤ value g :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem value_le_one {q : Nat} (g : Instance q) : value g ≤ 1 := by
  have hlength : (0 : ℝ) < g.constraints.length := by
    exact_mod_cast g.constraintCount_positive
  rw [value, div_le_iff₀ hlength, one_mul]
  exact_mod_cast maxSatisfied_le_length g

theorem value_mem_unitInterval {q : Nat} (g : Instance q) :
    value g ∈ Set.Icc (0 : ℝ) 1 := ⟨value_nonneg g, value_le_one g⟩

theorem exists_rate_ge_iff {q : Nat} (g : Instance q) (hq : 0 < q) (a : ℝ) :
    (∃ labeling : Fin g.vertices → Fin q,
      a ≤ (countSatisfied labeling g.constraints : ℝ) / g.constraints.length) ↔
      a ≤ value g := by
  constructor
  · rintro ⟨labeling, hlabeling⟩
    exact hlabeling.trans (labeling_rate_le_value g labeling)
  · intro hvalue
    obtain ⟨labeling, hlabeling⟩ := value_attained g hq
    exact ⟨labeling, hlabeling.symm ▸ hvalue⟩

theorem forall_rate_le_iff {q : Nat} (g : Instance q) (hq : 0 < q) (b : ℝ) :
    (∀ labeling : Fin g.vertices → Fin q,
      (countSatisfied labeling g.constraints : ℝ) / g.constraints.length ≤ b) ↔
      value g ≤ b := by
  constructor
  · intro hall
    obtain ⟨labeling, hlabeling⟩ := value_attained g hq
    exact hlabeling ▸ hall labeling
  · intro hvalue labeling
    exact (labeling_rate_le_value g labeling).trans hvalue

theorem completeAt_iff_value {q : Nat} (e : RationalError) (g : Instance q)
    (hq : 0 < q) :
    CompleteAt e g ↔ 1 - (GapSemantics.errorValue e : ℝ) ≤ value g := by
  rw [GapSemantics.completeAt_iff_real, exists_rate_ge_iff g hq]

theorem soundAt_iff_value {q : Nat} (e : RationalError) (g : Instance q)
    (hq : 0 < q) :
    SoundAt e g ↔ value g ≤ (GapSemantics.errorValue e : ℝ) := by
  rw [GapSemantics.soundAt_iff_real, forall_rate_le_iff g hq]

theorem realTarget_completeness {ε δ : ℝ}
    (p : RealTarget.PolynomialGapReduction ε δ) (formula : Formula)
    (hformula : formula.Satisfiable) :
    1 - ε ≤ value (p.reduce formula) := by
  have hq : 0 < p.alphabet := lt_of_lt_of_le (by decide : 0 < 2) p.alphabetAtLeastTwo
  exact (exists_rate_ge_iff (p.reduce formula) hq (1 - ε)).mp
    (p.completeness formula hformula)

theorem realTarget_soundness {ε δ : ℝ}
    (p : RealTarget.PolynomialGapReduction ε δ) (formula : Formula)
    (hformula : ¬ formula.Satisfiable) :
    value (p.reduce formula) ≤ δ := by
  have hq : 0 < p.alphabet := lt_of_lt_of_le (by decide : 0 < 2) p.alphabetAtLeastTwo
  exact (forall_rate_le_iff (p.reduce formula) hq δ).mp
    (p.soundness formula hformula)

theorem realTarget_value_guarantees {ε δ : ℝ}
    (p : RealTarget.PolynomialGapReduction ε δ) :
    Nonempty (Turing.TM2ComputableInPolyTime Complexity.formulaEncoding.encode
        (Complexity.gameEncoding p.alphabet).encode p.reduce) ∧
      (∀ formula : Formula, formula.Satisfiable → 1 - ε ≤ value (p.reduce formula)) ∧
      (∀ formula : Formula, ¬ formula.Satisfiable → value (p.reduce formula) ≤ δ) := by
  exact ⟨⟨p.computation⟩, realTarget_completeness p, realTarget_soundness p⟩

end DFVSGames.Integration.InstanceValue


namespace DFVSGames.Integration.BinaryCoordinates

abbrev Coordinates (n : Nat) := Fin n → Bool

def pack : {n : Nat} → Coordinates n → BitVec n
  | 0, _ => 0
  | _ + 1, f => BitVec.concat (pack (fun i => f i.succ)) (f 0)

def unpack {n : Nat} (v : BitVec n) : Coordinates n :=
  fun i => v.getLsbD i.val

theorem pack_get {n : Nat} (f : Coordinates n) (i : Fin n) :
    (pack f).getLsbD i.val = f i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact BitVec.getLsbD_concat_zero
    · exact (BitVec.getLsbD_concat_succ).trans (ih (fun j => f j.succ) j)

theorem unpack_pack {n : Nat} (f : Coordinates n) : unpack (pack f) = f := by
  funext i
  exact pack_get f i

theorem pack_unpack {n : Nat} (v : BitVec n) : pack (unpack v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  exact pack_get (unpack v) ⟨i, hi⟩

theorem unpack_injective {n : Nat} : Function.Injective (@unpack n) := by
  intro u v h
  have h' := congrArg pack h
  simpa only [pack_unpack] using h'

theorem pack_injective {n : Nat} : Function.Injective (@pack n) := by
  intro u v h
  have h' := congrArg unpack h
  simpa only [unpack_pack] using h'

theorem unpack_xor {n : Nat} (u v : BitVec n) :
    unpack (u ^^^ v) = fun i => (unpack u i ^^ unpack v i) := by
  funext i
  exact BitVec.getLsbD_xor

theorem pack_xor {n : Nat} (u v : Coordinates n) :
    pack (fun i => (u i ^^ v i)) = pack u ^^^ pack v := by
  apply unpack_injective
  rw [unpack_pack, unpack_xor, unpack_pack, unpack_pack]

theorem unpack_zero {n : Nat} : unpack (0 : BitVec n) = fun _ => false := by
  funext i
  simp [unpack]

theorem pack_zero {n : Nat} : pack (fun _ : Fin n => false) = 0 := by
  apply unpack_injective
  rw [unpack_pack, unpack_zero]

end DFVSGames.Integration.BinaryCoordinates


namespace DFVSGames.Integration.BinaryLinear

open BinaryCoordinates

abbrev F2 := ZMod 2
abbrev Vector (n : Nat) := Fin n → F2

def ofBit (b : Bool) : F2 := if b then 1 else 0
def toBit (a : F2) : Bool := decide (a = 1)

theorem scalar_cases : ∀ a : F2, a = 0 ∨ a = 1 := by decide
theorem ofBit_toBit : ∀ a : F2, ofBit (toBit a) = a := by decide
theorem toBit_ofBit : ∀ b : Bool, toBit (ofBit b) = b := by decide
theorem ofBit_xor : ∀ a b : Bool, ofBit (a ^^ b) = ofBit a + ofBit b := by decide
theorem toBit_add : ∀ a b : F2, toBit (a + b) = (toBit a ^^ toBit b) := by decide

def toVector {n : Nat} (v : BitVec n) : Vector n := fun i => ofBit (unpack v i)
def fromVector {n : Nat} (v : Vector n) : BitVec n := pack (fun i => toBit (v i))

theorem toVector_fromVector {n : Nat} (v : Vector n) : toVector (fromVector v) = v := by
  funext i
  simp only [toVector, fromVector, unpack_pack, ofBit_toBit]

theorem fromVector_toVector {n : Nat} (v : BitVec n) : fromVector (toVector v) = v := by
  simp only [fromVector, toVector, toBit_ofBit]
  exact pack_unpack v

def coordinatesEquiv (n : Nat) : BitVec n ≃ Vector n where
  toFun := toVector
  invFun := fromVector
  left_inv := fromVector_toVector
  right_inv := toVector_fromVector

theorem toVector_xor {n : Nat} (u v : BitVec n) :
    toVector (u ^^^ v) = toVector u + toVector v := by
  funext i
  simp only [toVector, unpack_xor, ofBit_xor, Pi.add_apply]

theorem fromVector_add {n : Nat} (u v : Vector n) :
    fromVector (u + v) = fromVector u ^^^ fromVector v := by
  simp only [fromVector, Pi.add_apply, toBit_add, pack_xor]

@[simp] theorem toVector_zero {n : Nat} : toVector (0 : BitVec n) = 0 := by
  unfold toVector
  rw [unpack_zero]
  rfl

@[simp] theorem fromVector_zero {n : Nat} : fromVector (0 : Vector n) = 0 := by
  simp [fromVector, toBit, pack_zero]

def liftLinear {n m : Nat} (f : BitVec n → BitVec m)
    (hzero : f 0 = 0) (hadd : ∀ x y, f (x ^^^ y) = f x ^^^ f y) :
    Vector n →ₗ[F2] Vector m where
  toFun x := toVector (f (fromVector x))
  map_add' x y := by rw [fromVector_add, hadd, toVector_xor]
  map_smul' c x := by
    rcases scalar_cases c with rfl | rfl
    · change toVector (f (fromVector (0 • x))) = 0 • toVector (f (fromVector x))
      rw [zero_smul, fromVector_zero, hzero, toVector_zero, zero_smul]
    · simp

theorem liftLinear_apply {n m : Nat} (f : BitVec n → BitVec m)
    (hzero : f 0 = 0) (hadd : ∀ x y, f (x ^^^ y) = f x ^^^ f y)
    (x : Vector n) :
    liftLinear f hzero hadd x = toVector (f (fromVector x)) := rfl

theorem finrank_vector (n : Nat) : Module.finrank F2 (Vector n) = n := by
  simp [Vector]

end DFVSGames.Integration.BinaryLinear


namespace DFVSGames.Integration.TranslationTarget

open DFVSGames.Foundations
open Target

def IsTranslationInstance {q s : Nat} (coordinates : Fin q ≃ BinaryLinear.Vector s)
    (g : Instance q) : Prop :=
  ∀ constraint ∈ g.constraints, ∃ shift : BinaryLinear.Vector s,
    ∀ label : Fin q,
      coordinates (constraint.permutation.images[label]) = coordinates label + shift

structure PolynomialGapReduction (ε δ : ℝ) extends RealTarget.PolynomialGapReduction ε δ where
  dimension : Nat
  coordinates : Fin alphabet ≃ BinaryLinear.Vector dimension
  translations : ∀ formula : Formula,
    IsTranslationInstance coordinates (reduce formula)

def ofRational {e d : RationalError} {ε δ : ℝ}
    (p : Complexity.PolynomialGapReduction e d) (s : Nat)
    (coordinates : Fin p.alphabet ≃ BinaryLinear.Vector s)
    (translations : ∀ formula, IsTranslationInstance coordinates (p.reduce formula))
    (hε : (GapSemantics.errorValue e : ℝ) ≤ ε)
    (hδ : (GapSemantics.errorValue d : ℝ) ≤ δ) : PolynomialGapReduction ε δ where
  toPolynomialGapReduction := RealTarget.ofRational p hε hδ
  dimension := s
  coordinates := coordinates
  translations := translations

theorem for_all_real_of_dyadic
    (certificates : ∀ m n : Nat,
      ∃ p : Complexity.PolynomialGapReduction
        (DyadicErrors.dyadicError m) (DyadicErrors.dyadicError n),
      ∃ s : Nat, ∃ coordinates : Fin p.alphabet ≃ BinaryLinear.Vector s,
        ∀ formula, IsTranslationInstance coordinates (p.reduce formula))
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    Nonempty (PolynomialGapReduction ε δ) := by
  obtain ⟨m, hm⟩ := DyadicErrors.exists_dyadic_below_real hε
  obtain ⟨n, hn⟩ := DyadicErrors.exists_dyadic_below_real hδ
  obtain ⟨p, s, coordinates, translations⟩ := certificates m n
  exact ⟨ofRational p s coordinates translations hm.le hn.le⟩

end DFVSGames.Integration.TranslationTarget


namespace DFVSGames.Explicit.UniformTarget

open DFVSGames.Foundations Target Complexity
open DFVSGames.Integration
open MachineUniformCopyOrder

theorem copy_length {α : Type*} (C : Nat) (xs : List α) :
    (copyMajor C xs).length = C * xs.length := by
  induction C with
  | zero => simp [copyMajor]
  | succ C ih =>
    simp [copyMajor, List.replicate_succ, List.flatten_cons, Nat.add_mul,
      Nat.add_comm]

def construct {q : Nat} (C : Nat) (hC : 0 < C) (g : Instance q) : Instance q where
  vertices := g.vertices
  constraints := copyMajor C g.constraints
  nonempty := by
    apply List.length_pos_iff.mp
    rw [copy_length]
    exact Nat.mul_pos hC g.constraintCount_positive

@[simp] theorem vertices {q : Nat} (C : Nat) (hC : 0 < C) (g : Instance q) :
    (construct C hC g).vertices = g.vertices := rfl

@[simp] theorem edge_count {q : Nat} (C : Nat) (hC : 0 < C) (g : Instance q) :
    (construct C hC g).constraints.length = C * g.constraints.length :=
  copy_length C g.constraints

private theorem count_append_inline_UniformTarget {n q : Nat} (a : Fin n → Fin q)
    (xs ys : List (Constraint n q)) :
    countSatisfied a (xs ++ ys) = countSatisfied a xs + countSatisfied a ys := by
  simp [GapSemantics.countSatisfied_eq_sum]

theorem count_copies {n q : Nat} (C : Nat) (es : List (Constraint n q))
    (a : Fin n → Fin q) :
    countSatisfied a (copyMajor C es) = C * countSatisfied a es := by
  induction C with
  | zero => simp [copyMajor, countSatisfied]
  | succ C ih =>
    change countSatisfied a (es ++ copyMajor C es) = _
    rw [count_append_inline_UniformTarget, ih, Nat.add_mul, Nat.one_mul]
    omega

theorem count {q : Nat} (C : Nat) (hC : 0 < C) (g : Instance q)
    (a : Fin g.vertices → Fin q) :
    countSatisfied a (construct C hC g).constraints = C * countSatisfied a g.constraints :=
  count_copies C g.constraints a

theorem maxSatisfied {q : Nat} (C : Nat) (hC : 0 < C) (g : Instance q) (hq : 0 < q) :
    InstanceValue.maxSatisfied (construct C hC g) = C * InstanceValue.maxSatisfied g := by
  classical
  apply Nat.le_antisymm
  · unfold InstanceValue.maxSatisfied
    apply Finset.sup_le
    intro a _
    change Fin g.vertices → Fin q at a
    change countSatisfied a (copyMajor C g.constraints) ≤ C * InstanceValue.maxSatisfied g
    rw [count_copies]
    exact Nat.mul_le_mul_left C (InstanceValue.countSatisfied_le_maxSatisfied g a)
  · obtain ⟨a, ha⟩ := InstanceValue.maxSatisfied_attained g hq
    rw [← ha, ← count C hC g a]
    exact InstanceValue.countSatisfied_le_maxSatisfied (construct C hC g) a

theorem value {q : Nat} (C : Nat) (hC : 0 < C) (g : Instance q) (hq : 0 < q) :
    InstanceValue.value (construct C hC g) = InstanceValue.value g := by
  have hc : (C : ℝ) ≠ 0 := by exact_mod_cast hC.ne'
  have hm : (g.constraints.length : ℝ) ≠ 0 := by
    exact_mod_cast g.constraintCount_positive.ne'
  unfold InstanceValue.value
  rw [maxSatisfied C hC g hq, edge_count]
  push_cast
  field_simp

theorem mem_original {q : Nat} (C : Nat) (hC : 0 < C) (g : Instance q)
    (c : Constraint g.vertices q) (hc : c ∈ (construct C hC g).constraints) :
    c ∈ g.constraints := by
  obtain ⟨es, hes, hc⟩ := List.mem_flatten.mp hc
  have he : es = g.constraints := List.eq_of_mem_replicate hes
  simpa [he] using hc

theorem translations {q s : Nat} (C : Nat) (hC : 0 < C) (g : Instance q)
    (coordinates : Fin q ≃ BinaryLinear.Vector s)
    (hg : TranslationTarget.IsTranslationInstance coordinates g) :
    TranslationTarget.IsTranslationInstance coordinates (construct C hC g) := by
  intro c hc
  exact hg c (mem_original C hC g c hc)

theorem flatMap_copies {α β : Type*} (C : Nat) (xs : List α) (f : α → List β) :
    (copyMajor C xs).flatMap f = copyMajor C (xs.flatMap f) := by
  induction C with
  | zero => simp [copyMajor]
  | succ C ih =>
    simpa only [copyMajor, List.replicate_succ, List.flatten_cons,
      List.flatMap_append] using congrArg (fun ys => xs.flatMap f ++ ys) ih

theorem encode_copies (C : Nat) (words : List Nat) :
    encodeWords (copyMajor C words) = copyMajor C (encodeWords words) := by
  induction C with
  | zero => rfl
  | succ C ih =>
    simpa only [copyMajor, List.replicate_succ, List.flatten_cons,
      encodeWords_append] using congrArg (fun xs => encodeWords words ++ xs) ih

theorem gameWords_construct {q : Nat} (C : Nat) (hC : 0 < C) (g : Instance q) :
    gameWords (construct C hC g) =
      [g.vertices, q, C * g.constraints.length] ++
        copyMajor C (g.constraints.flatMap constraintWords) := by
  simp only [gameWords, vertices]
  rw [show (construct C hC g).constraints = copyMajor C g.constraints from rfl,
    flatMap_copies, copy_length]

theorem gameBits_construct {q : Nat} (C : Nat) (hC : 0 < C) (g : Instance q) :
    gameBits (construct C hC g) =
      encodeWords [g.vertices, q, C * g.constraints.length] ++
        copyMajor C (encodeWords (g.constraints.flatMap constraintWords)) := by
  rw [gameBits, gameWords_construct, encodeWords_append, encode_copies]

end DFVSGames.Explicit.UniformTarget

end OAI
