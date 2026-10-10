import Mathlib
import OAI.Computability.DirectedFeedback.RankGraph.StackFinite

namespace OAI


noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.SumBox
variable (A B : Type) [Fintype A] [Fintype B] [Nonempty (A ⊕ B)]
variable (n m L r : Nat) (c : B → Nat)
abbrev Live := ((A × (Fin L → Fin n)) × Fin r) ⊕ (Σ s : B, (Fin L → Fin m) × Fin (c s))
def base : Nat := n+m+1
def copies {B : Type} [Fintype B] (r : Nat) (c : B → Nat) : Nat := r+(∑ s,c s)+1

theorem base_pos : 0<base n m := by unfold base; omega
theorem copies_pos {B : Type} [Fintype B] (r : Nat) (c : B → Nat) : 0<copies r c := by unfold copies; omega
theorem c_le {B : Type} [Fintype B] (r : Nat) (c : B → Nat) (s : B) : c s≤copies r c := by
  have hs := Finset.single_le_sum (fun s _ => Nat.zero_le (c s)) (Finset.mem_univ s)
  unfold copies
  omega

def toBox : Live A B n m L r c → BoxCodec.Box (A ⊕ B) (base n m) (copies r c) L
  | .inl ((s,a),j) => (.inl s, (fun i => ⟨a i,by have := (a i).isLt; unfold base; omega⟩),
      ⟨j,by have := j.isLt; unfold copies; omega⟩)
  | .inr ⟨s,a,j⟩ => (.inr s,(fun i => ⟨a i,by have := (a i).isLt; unfold base; omega⟩),
      ⟨j,lt_of_lt_of_le j.isLt (c_le r c s)⟩)

def validBox (z : BoxCodec.Box (A ⊕ B) (base n m) (copies r c) L) : Prop :=
  match z.1 with
  | .inl _ => (∀ i, (z.2.1 i).val < n) ∧ z.2.2.val < r
  | .inr s => (∀ i, (z.2.1 i).val < m) ∧ z.2.2.val < c s

omit [Fintype A] [Nonempty (A ⊕ B)] in
theorem toBox_injective : Function.Injective (toBox A B n m L r c) := by
  intro x y h
  rcases x with ⟨⟨s,a⟩,j⟩ | ⟨s,a,j⟩ <;> rcases y with ⟨⟨t,b⟩,k⟩ | ⟨t,b,k⟩
  · have hh := Prod.mk.inj h
    have hst : s=t := Sum.inl.inj hh.1
    subst t
    have hab : a=b := by
      funext i
      apply Fin.ext
      exact congrArg (fun z => (z.1 i).val) hh.2
    have hjk : j=k := Fin.ext (congrArg (fun z => z.2.val) hh.2)
    simp [hab,hjk]
  · have hh := congrArg (fun z : BoxCodec.Box (A ⊕ B) (base n m) (copies r c) L => z.1) h
    simp only [toBox] at hh
    cases hh
  · have hh := congrArg (fun z : BoxCodec.Box (A ⊕ B) (base n m) (copies r c) L => z.1) h
    simp only [toBox] at hh
    cases hh
  · have hh := Prod.mk.inj h
    have hst : s=t := Sum.inr.inj hh.1
    subst t
    have hab : a=b := by
      funext i
      apply Fin.ext
      exact congrArg (fun z => (z.1 i).val) hh.2
    have hjk : j=k := Fin.ext (congrArg (fun z => z.2.val) hh.2)
    simp [hab,hjk]

omit [Fintype A] [Nonempty (A ⊕ B)] in
theorem validBox_toBox (v : Live A B n m L r c) : validBox A B n m L r c (toBox A B n m L r c v) := by
  rcases v with ⟨⟨s,a⟩,j⟩ | ⟨s,a,j⟩ <;> exact ⟨fun i => (a i).isLt,j.isLt⟩

omit [Fintype A] [Nonempty (A ⊕ B)] in
theorem validBox_surjective (z : BoxCodec.Box (A ⊕ B) (base n m) (copies r c) L)
    (hz : validBox A B n m L r c z) : ∃ v, toBox A B n m L r c v=z := by
  rcases z with ⟨s|s,a,j⟩
  · refine ⟨.inl ((s,fun i => ⟨(a i).val,hz.1 i⟩),⟨j.val,hz.2⟩),?_⟩
    rfl
  · refine ⟨.inr ⟨s,(fun i => ⟨(a i).val,hz.1 i⟩),⟨j.val,hz.2⟩⟩,?_⟩
    rfl

def size := BoxCodec.size (A ⊕ B) (base n m) (copies r c) L
def tag (i : Nat) := BoxCodec.tag (A ⊕ B) (base n m) (copies r c) L i
def digits (i : Nat) := BoxCodec.digits (base n m) (copies r c) L i
def copy (i : Nat) := BoxCodec.copy (base n m) (copies r c) L i
def embed (v : Live A B n m L r c) : Fin (size A B n m L r c) :=
  BoxCodec.equiv (A ⊕ B) (base n m) (copies r c) L (base_pos n m) (toBox A B n m L r c v)
def valid (i : Nat) : Prop :=
  match tag A B n m L r c i with
  | .inl _ => (∀ j, digits B n m L r c i j < n) ∧ copy B n m L r c i < r
  | .inr s => (∀ j, digits B n m L r c i j < m) ∧ copy B n m L r c i < c s

omit [Nonempty (A ⊕ B)] in
theorem embed_injective : Function.Injective (embed A B n m L r c) :=
  (BoxCodec.equiv (A ⊕ B) (base n m) (copies r c) L (base_pos n m)).injective.comp
    (toBox_injective A B n m L r c)

theorem valid_iff (i : Fin (size A B n m L r c)) : valid A B n m L r c i.val ↔
    validBox A B n m L r c ((BoxCodec.equiv (A ⊕ B) (base n m) (copies r c) L (base_pos n m)).symm i) := by
  unfold valid tag digits copy validBox
  rw [BoxCodec.decode_tag (A ⊕ B) (base n m) (copies r c) L (base_pos n m) i]
  simp_rw [BoxCodec.decode_digits (A ⊕ B) (base n m) (copies r c) L (base_pos n m) i,
    BoxCodec.decode_copy (A ⊕ B) (base n m) (copies r c) L (base_pos n m) i]

theorem valid_embed (v : Live A B n m L r c) : valid A B n m L r c (embed A B n m L r c v).val := by
  rw [valid_iff]
  simpa only [embed,Equiv.symm_apply_apply] using validBox_toBox A B n m L r c v

theorem valid_surjective (i : Fin (size A B n m L r c)) (hi : valid A B n m L r c i.val) :
    ∃ v, embed A B n m L r c v=i := by
  obtain ⟨v,hv⟩ := validBox_surjective A B n m L r c _ ((valid_iff A B n m L r c i).mp hi)
  refine ⟨v,?_⟩
  unfold embed
  rw [hv]
  exact (BoxCodec.equiv (A ⊕ B) (base n m) (copies r c) L (base_pos n m)).apply_symm_apply i

theorem tag_embed (v : Live A B n m L r c) :
    tag A B n m L r c (embed A B n m L r c v).val=(toBox A B n m L r c v).1 :=
  BoxCodec.tag_equiv _ _ _ _ _ _
omit [Nonempty (A ⊕ B)] in
theorem digits_embed (v : Live A B n m L r c) (j : Fin L) :
    digits B n m L r c (embed A B n m L r c v).val j=((toBox A B n m L r c v).2.1 j).val :=
  BoxCodec.digits_equiv _ _ _ _ _ _ _
omit [Nonempty (A ⊕ B)] in
theorem copy_embed (v : Live A B n m L r c) :
    copy B n m L r c (embed A B n m L r c v).val=(toBox A B n m L r c v).2.2.val :=
  BoxCodec.copy_equiv _ _ _ _ _ _

end DirectedFeedback.SumBox

end


noncomputable section
open scoped Classical
namespace DirectedFeedback.BoundedExpr
variable {r : Nat} {A B : Type} [Fintype A] [Fintype B]

structure LDef (l : List Bool → (Fin r → Nat) → List A) : Prop where
  length : Def (fun x a => (l x a).length)
  get : ∀ i, Def i → FDef (fun x a => (l x a)[i x a]?)

namespace LDef
variable {l m : List Bool → (Fin r → Nat) → List A}

omit [Fintype A] in
theorem congr (hl : LDef l) (h : ∀ x a, l x a=m x a) : LDef m := by
  have he : l=m := funext (fun x => funext (h x))
  rwa [← he]

omit [Fintype A] in
theorem const (l : List A) : LDef (fun (_ : List Bool) (_ : Fin r → Nat) => l) := by
  constructor
  · exact Def.lit l.length
  · intro i hi
    apply (FDef.ofNat hi l.length (fun j => some l[j.val]) none).congr
    intro x a
    by_cases h : i x a<l.length
    · simp [h]
    · simp [h]

theorem input : LDef (fun (x : List Bool) (_ : Fin r → Nat) => x) := by
  constructor
  · exact Def.length
  · intro i hi
    apply ((PDef.lt hi Def.length).ite ((FDef.bool hi.bit).map some) (FDef.const none)).congr
    intro x a
    by_cases h : i x a<x.length
    · simp [h]
    · simp [h]

omit [Fintype A] in
theorem replicate {n : List Bool → (Fin r → Nat) → Nat} (hn : Def n) (v : A) :
    LDef (fun x a => List.replicate (n x a) v) := by
  constructor
  · simpa only [List.length_replicate] using hn
  · intro i hi
    exact ((PDef.lt hi hn).ite (FDef.const (some v)) (FDef.const none)).congr
      (by intro x a; by_cases h : i x a<n x a <;> simp [h])

omit [Fintype A] in
theorem append (hl : LDef l) (hm : LDef m) : LDef (fun x a => l x a++m x a) := by
  constructor
  · simpa only [List.length_append] using hl.length.add hm.length
  · intro i hi
    apply ((PDef.lt hi hl.length).ite (hl.get i hi) (hm.get _ (hi.sub hl.length))).congr
    intro x a
    by_cases h : i x a < (l x a).length <;> simp [List.getElem?_append,h]

omit [Fintype B] in
theorem map (hl : LDef l) (f : A → B) : LDef (fun x a => (l x a).map f) := by
  constructor
  · simpa only [List.length_map] using hl.length
  · intro i hi
    exact ((hl.get i hi).map (Option.map f)).congr (by intro x a; simp)
end LDef
end DirectedFeedback.BoundedExpr

end


namespace DFVSGames.BinaryFormula

structure Literal where
  name : Nat
  positive : Bool
  deriving DecidableEq

def Literal.eval (literal : Literal) (assignment : Nat → Bool) : Bool :=
  if literal.positive then assignment literal.name else !(assignment literal.name)

abbrev Clause := Vector Literal 3

def Clause.eval (clause : Clause) (assignment : Nat → Bool) : Bool :=
  (clause[0].eval assignment || clause[1].eval assignment) || clause[2].eval assignment

structure Formula where
  clauses : List Clause

def Formula.Satisfiable (F : Formula) : Prop :=
  ∃ assignment : Nat → Bool, ∀ clause ∈ F.clauses, clause.eval assignment = true

def clauseNames (clause : Clause) : List Nat :=
  [clause[0].name, clause[1].name, clause[2].name]

end DFVSGames.BinaryFormula

namespace DFVSGames.BinaryEncoding

open BinaryFormula

def bitsValue : List Bool → Nat
  | [] => 0
  | b :: bits => Nat.bit b (bitsValue bits)

@[simp] theorem bitsValue_bits (n : Nat) : bitsValue n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [bitsValue]
  | bit b n hn ih =>
      rw [Nat.bits_append_bit n b hn]
      simp only [bitsValue, ih]

def frame : List Bool → List Bool
  | [] => [false]
  | b :: bits => true :: b :: frame bits

def parseFrame : List Bool → Option (List Bool × List Bool)
  | false :: rest => some ([], rest)
  | true :: b :: rest => do
      let (bits, trailing) ← parseFrame rest
      return (b :: bits, trailing)
  | _ => none

@[simp] theorem parseFrame_encoded (bits trailing : List Bool) :
    parseFrame (frame bits ++ trailing) = some (bits, trailing) := by
  induction bits with
  | nil => rfl
  | cons b bits ih => simp [frame, parseFrame, ih]

@[simp] theorem frame_length (bits : List Bool) :
    (frame bits).length = 2 * bits.length + 1 := by
  induction bits with
  | nil => rfl
  | cons b bits ih => simp [frame, ih]; omega

def nameBits (name : Nat) : List Bool := frame name.bits

def parseName (input : List Bool) : Option (Nat × List Bool) := do
  let (digits, rest) ← parseFrame input
  let name := bitsValue digits
  if digits = name.bits then some (name, rest) else none

@[simp] theorem parseName_encoded (name : Nat) (rest : List Bool) :
    parseName (nameBits name ++ rest) = some (name, rest) := by
  simp [parseName, nameBits]

@[simp] theorem nameBits_length (name : Nat) :
    (nameBits name).length = 2 * name.size + 1 := by
  simp [nameBits, Nat.size_eq_bits_len]

theorem nameBits_length_le_of_lt_pow (name width : Nat) (bound : name < 2 ^ width) :
    (nameBits name).length ≤ 2 * width + 1 := by
  rw [nameBits_length]
  have h := Nat.size_le.mpr bound
  omega

def literalBits (literal : Literal) : List Bool :=
  literal.positive :: nameBits literal.name

def parseLiteral : List Bool → Option (Literal × List Bool)
  | sign :: input => do
      let (name, rest) ← parseName input
      return (⟨name, sign⟩, rest)
  | [] => none

@[simp] theorem parseLiteral_encoded (literal : Literal) (rest : List Bool) :
    parseLiteral (literalBits literal ++ rest) = some (literal, rest) := by
  cases literal with
  | mk name sign => simp [literalBits, parseLiteral]

@[simp] theorem literalBits_length (literal : Literal) :
    (literalBits literal).length = 2 * literal.name.size + 2 := by
  simp [literalBits]

def clauseBits (clause : Clause) : List Bool :=
  literalBits clause[0] ++ literalBits clause[1] ++ literalBits clause[2]

def parseClause (input : List Bool) : Option (Clause × List Bool) := do
  let (a, input) ← parseLiteral input
  let (b, input) ← parseLiteral input
  let (c, rest) ← parseLiteral input
  return (#v[a, b, c], rest)

theorem clause_three_entries (clause : Clause) : #v[clause[0], clause[1], clause[2]] = clause := by
  apply Vector.ext
  intro i hi
  have cases_i : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases cases_i with rfl | rfl | rfl <;> rfl

@[simp] theorem parseClause_encoded (clause : Clause) (rest : List Bool) :
    parseClause (clauseBits clause ++ rest) = some (clause, rest) := by
  simp [clauseBits, List.append_assoc, parseClause, clause_three_entries]

def clauseNameSize (clause : Clause) : Nat :=
  ((clauseNames clause).map Nat.size).sum

@[simp] theorem clauseBits_length (clause : Clause) :
    (clauseBits clause).length = 2 * clauseNameSize clause + 6 := by
  simp [clauseBits, clauseNameSize, clauseNames]
  omega

def clausesBits : List Clause → List Bool
  | [] => [false]
  | clause :: clauses => true :: (clauseBits clause ++ clausesBits clauses)

def formulaBits (formula : Formula) : List Bool := clausesBits formula.clauses

def namesBitSize (clauses : List Clause) : Nat :=
  ((clauses.flatMap clauseNames).map Nat.size).sum

@[simp] theorem namesBitSize_nil : namesBitSize [] = 0 := rfl

@[simp] theorem namesBitSize_cons (clause : Clause) (clauses : List Clause) :
    namesBitSize (clause :: clauses) = clauseNameSize clause + namesBitSize clauses := by
  simp [namesBitSize, clauseNameSize]

theorem clausesBits_length (clauses : List Clause) :
    (clausesBits clauses).length = 7 * clauses.length + 2 * namesBitSize clauses + 1 := by
  induction clauses with
  | nil => rfl
  | cons clause clauses ih =>
      simp only [clausesBits, List.length_cons, List.length_append, clauseBits_length,
        namesBitSize_cons, ih]
      omega

theorem formulaBits_length (formula : Formula) :
    (formulaBits formula).length =
      7 * formula.clauses.length + 2 * namesBitSize formula.clauses + 1 :=
  clausesBits_length formula.clauses

theorem clauses_length_lt_bits (clauses : List Clause) :
    clauses.length < (clausesBits clauses).length := by
  rw [clausesBits_length]
  omega

def ordinarySize (formula : Formula) : Nat :=
  3 * formula.clauses.length + namesBitSize formula.clauses + 1

theorem ordinarySize_le_bits (formula : Formula) :
    ordinarySize formula ≤ (formulaBits formula).length := by
  rw [formulaBits_length]
  unfold ordinarySize
  omega

theorem bits_le_three_ordinarySize (formula : Formula) :
    (formulaBits formula).length ≤ 3 * ordinarySize formula := by
  rw [formulaBits_length]
  unfold ordinarySize
  omega

def parseClauses : Nat → List Bool → Option (List Clause × List Bool)
  | 0, _ => none
  | _ + 1, false :: rest => some ([], rest)
  | fuel + 1, true :: input => do
      let (clause, input) ← parseClause input
      let (clauses, rest) ← parseClauses fuel input
      return (clause :: clauses, rest)
  | _ + 1, [] => none

@[simp] theorem parseClauses_encoded (clauses : List Clause) (rest : List Bool)
    (fuel : Nat) (enough : clauses.length < fuel) :
    parseClauses fuel (clausesBits clauses ++ rest) = some (clauses, rest) := by
  induction clauses generalizing fuel with
  | nil =>
      cases fuel with
      | zero => omega
      | succ fuel => simp [clausesBits, parseClauses]
  | cons clause clauses ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hrest : clauses.length < fuel := by simp only [List.length_cons] at enough; omega
          simp [clausesBits, parseClauses, List.append_assoc, ih fuel hrest]

def decodeFormula (input : List Bool) : Option Formula := do
  let (clauses, rest) ← parseClauses (input.length + 1) input
  if rest = [] then some ⟨clauses⟩ else none

@[simp] theorem decodeFormula_encoded (formula : Formula) :
    decodeFormula (formulaBits formula) = some formula := by
  cases formula with
  | mk clauses =>
      have hlen := clauses_length_lt_bits clauses
      have parsed := parseClauses_encoded clauses [] ((clausesBits clauses).length + 1) (by omega)
      simp only [List.append_nil] at parsed
      simp [formulaBits, decodeFormula, parsed]

theorem formulaBits_injective {first second : Formula}
    (same : formulaBits first = formulaBits second) : first = second := by
  have parsed := congrArg decodeFormula same
  simpa only [decodeFormula_encoded, Option.some.injEq] using parsed

end DFVSGames.BinaryEncoding

namespace DFVSMaxCut

open scoped BigOperators

noncomputable def alphaGW : ℝ :=
  sInf ((fun ρ : ℝ => 2 * Real.arccos ρ / (Real.pi * (1 - ρ))) ''
    Set.Ico (-1 : ℝ) 1)

def binary3SAT (input : List Bool) : Prop :=
  ∃ formula, DFVSGames.BinaryEncoding.decodeFormula input = some formula ∧
    formula.Satisfiable

structure Graph where
  vertices : ℕ
  adj : Fin vertices → Fin vertices → Bool
  symmetric : ∀ u v, adj u v = adj v u
  loopless : ∀ u, adj u u = false

def Graph.cutSize (G : Graph) (cut : Fin G.vertices → Bool) : ℕ :=
  ∑ u : Fin G.vertices, ∑ v : Fin G.vertices,
    if u < v ∧ G.adj u v = true ∧ cut u ≠ cut v then 1 else 0

def Graph.maxCut (G : Graph) : ℕ :=
  (Finset.univ.image G.cutSize).sup id

structure ScaledGraph where
  graph : Graph
  scale : ℕ
  scale_pos : 0 < scale

def ScaledGraph.bits (G : ScaledGraph) : List Bool :=
  DFVSGames.BinaryEncoding.nameBits G.graph.vertices ++
  DFVSGames.BinaryEncoding.nameBits G.scale ++
  (List.finRange G.graph.vertices).flatMap (fun u =>
    (List.finRange G.graph.vertices).map (fun v => G.graph.adj u v))

structure GapReduction (α : ℝ) where
  yesBound : ℚ
  noBound : ℚ
  yes_pos : 0 < yesBound
  no_nonneg : 0 ≤ noBound
  gap : (noBound : ℝ) < α * (yesBound : ℝ)
  construct : List Bool → ScaledGraph
  computation : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool)
    ScaledGraph.bits construct
  finiteAlphabet : ∀ k, Finite (computation.tm.Γ k)
  completeness : ∀ input, binary3SAT input →
    (yesBound : ℝ) ≤ ((construct input).graph.maxCut : ℝ) / (construct input).scale
  soundness : ∀ input, ¬ binary3SAT input →
    ((construct input).graph.maxCut : ℝ) / (construct input).scale ≤ (noBound : ℝ)

def MainStatement : Prop :=
  ∀ α : ℝ, alphaGW < α → α ≤ 1 → Nonempty (GapReduction α)

end DFVSMaxCut


namespace DFVSGames.Repetition

noncomputable def dsRate (gap : ℝ) : ℝ := 1 - gap ^ 2 / 16

theorem dsRate_nonneg {gap : ℝ} (hgap₀ : 0 ≤ gap) (hgap₁ : gap ≤ 1) :
    0 ≤ dsRate gap := by
  dsimp [dsRate]
  nlinarith

theorem dsRate_lt_one {gap : ℝ} (hgap : 0 < gap) : dsRate gap < 1 := by
  dsimp [dsRate]
  nlinarith [sq_pos_of_pos hgap]

theorem exists_positive_power_lt {rate error : ℝ}
    (hrate₀ : 0 ≤ rate) (hrate₁ : rate < 1) (herror : 0 < error) :
    ∃ n : ℕ, 1 ≤ n ∧ rate ^ n < error := by
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one hrate₀ hrate₁
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds herror)).exists
  refine ⟨n + 1, Nat.succ_le_succ (Nat.zero_le n), ?_⟩
  calc
    rate ^ (n + 1) = rate ^ n * rate := pow_succ _ _
    _ ≤ rate ^ n := mul_le_of_le_one_right (pow_nonneg hrate₀ n) hrate₁.le
    _ < error := hn

theorem exists_dsRate_pow_le {gap error : ℝ}
    (hgap₀ : 0 < gap) (hgap₁ : gap < 1) (herror : 0 < error) :
    ∃ n : ℕ, 1 ≤ n ∧ dsRate gap ^ n ≤ error := by
  obtain ⟨n, hn, hbound⟩ := exists_positive_power_lt
    (dsRate_nonneg hgap₀.le hgap₁.le) (dsRate_lt_one hgap₀) herror
  exact ⟨n, hn, hbound.le⟩

theorem dsRate_one_div_eight_hundred :
    dsRate (1 / 800) = 1 - (1 : ℝ) / 10240000 := by
  norm_num [dsRate]

theorem dsRate_one_div_fifteen :
    dsRate (1 / 15) = 1 - (1 : ℝ) / 3600 := by
  norm_num [dsRate]

theorem exists_final_repetition_count {error : ℝ} (herror : 0 < error) :
    ∃ n : ℕ, 1 ≤ n ∧ (1 - (1 : ℝ) / 10240000) ^ n ≤ error := by
  simpa only [dsRate_one_div_eight_hundred] using
    exists_dsRate_pow_le (gap := (1 / 800 : ℝ)) (by norm_num) (by norm_num) herror

theorem exists_preliminary_repetition_count {error : ℝ} (herror : 0 < error) :
    ∃ n : ℕ, 1 ≤ n ∧ (1 - (1 : ℝ) / 3600) ^ n ≤ error := by
  simpa only [dsRate_one_div_fifteen] using
    exists_dsRate_pow_le (gap := (1 / 15 : ℝ)) (by norm_num) (by norm_num) herror

end DFVSGames.Repetition


namespace DFVSGames.Explicit.FinishBounds

theorem exists_reciprocal_tolerance (ε : ℚ) (hε : 0 < ε) (t : Nat) (ht : 0 < t) :
    ∃ C : Nat, 200 ≤ C ∧ (0 : ℚ) < 1 / C ∧
      1 / (C : ℚ) ≤ 1 / 200 ∧ 1 / (C : ℚ) ≤ ε / t := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((t : ℚ) / ε)
  let C := n + 200
  have hC : (0 : ℚ) < C := by dsimp [C]; positivity
  have ht' : (0 : ℚ) < t := by exact_mod_cast ht
  have hCn : (n : ℚ) ≤ C := by dsimp [C]; exact_mod_cast Nat.le_add_right n 200
  have hbound : (t : ℚ) / ε < C := lt_of_lt_of_le hn hCn
  have hbudget : (t : ℚ) ≤ ε * C := by
    have he := (div_lt_iff₀ hε).mp hbound
    nlinarith
  refine ⟨C, by dsimp [C]; omega, one_div_pos.mpr hC, ?_, ?_⟩
  · apply one_div_le_one_div_of_le (by norm_num : (0 : ℚ) < 200)
    dsimp [C]
    exact_mod_cast Nat.le_add_left 200 n
  · apply (div_le_div_iff₀ hC ht').mpr
    simpa [mul_comm] using hbudget

theorem subdivision_completeness (vH vB d τ : ℝ)
    (hH : 1 - d ≤ vH)
    (hround : |vB - (1 - (1 - vH) / 4)| ≤ τ / 4) :
    1 - (d + τ) / 4 ≤ vB := by
  have h := (abs_le.mp hround).1
  linarith

theorem subdivision_soundness (vH vB τ : ℝ)
    (hH : vH ≤ 99 / 100) (hτ : τ ≤ 1 / 200)
    (hround : |vB - (1 - (1 - vH) / 4)| ≤ τ / 4) :
    vB ≤ 1 - 1 / 800 := by
  have h := (abs_le.mp hround).2
  linarith

theorem final_completeness (vB vG d τ ε₀ ε : ℝ) (t : Nat) (ht : 0 < t)
    (hB : 1 - (d + τ) / 4 ≤ vB)
    (hG : 1 - (t : ℝ) * (1 - vB) ≤ vG)
    (hd : d ≤ ε₀ / t) (hτ : τ ≤ ε₀ / t)
    (hε₀ : 0 ≤ ε₀) (hε : ε₀ ≤ ε) :
    1 - ε ≤ vG := by
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  have hd' := (le_div_iff₀ ht').mp hd
  have hτ' := (le_div_iff₀ ht').mp hτ
  have hB' : (t : ℝ) * (1 - vB) ≤ t * ((d + τ) / 4) :=
    mul_le_mul_of_nonneg_left (by linarith) ht'.le
  nlinarith

end DFVSGames.Explicit.FinishBounds


namespace DFVSGames.ParameterSelection
noncomputable section

structure OuterParameters (ε δ : ℝ) where
  epsilon0 : ℚ
  delta0 : ℚ
  epsilon0_pos : 0 < epsilon0
  delta0_pos : 0 < delta0
  epsilon0_le : (epsilon0 : ℝ) ≤ ε
  delta0_le : (delta0 : ℝ) ≤ δ
  repetitions : ℕ
  repetitions_pos : 0 < repetitions
  soundness_rate : (1 - (1 : ℝ) / 10240000) ^ repetitions ≤ delta0
  copies : ℕ
  copies_large : 200 ≤ copies
  reciprocal_pos : (0 : ℚ) < 1 / copies
  reciprocal_small : 1 / (copies : ℚ) ≤ 1 / 200
  reciprocal_budget : 1 / (copies : ℚ) ≤ epsilon0 / repetitions

theorem exists_outerParameters (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    Nonempty (OuterParameters ε δ) := by
  obtain ⟨ε₀, hε₀, hεbound⟩ := exists_rat_btwn hε
  obtain ⟨δ₀, hδ₀, hδbound⟩ := exists_rat_btwn hδ
  have hεq : (0 : ℚ) < ε₀ := by exact_mod_cast hε₀
  have hδq : (0 : ℚ) < δ₀ := by exact_mod_cast hδ₀
  obtain ⟨t, ht, hrate⟩ := Repetition.exists_final_repetition_count hδ₀
  have htpos : 0 < t := ht
  obtain ⟨C, hC, hCpos, hCsmall, hCbudget⟩ :=
    Explicit.FinishBounds.exists_reciprocal_tolerance ε₀ hεq t htpos
  exact ⟨⟨ε₀, δ₀, hεq, hδq, hεbound.le, hδbound.le,
    t, htpos, hrate, C, hC, hCpos, hCsmall, hCbudget⟩⟩

namespace OuterParameters

variable {ε δ : ℝ} (P : OuterParameters ε δ)

def pStar : ℚ := 1 / P.copies

theorem pStar_pos : 0 < P.pStar := P.reciprocal_pos

theorem pStar_lt_one : P.pStar < 1 :=
  P.reciprocal_small.trans_lt (by norm_num)

theorem exists_parity_error (k : ℕ) (hk : 0 < k) :
    ∃ ξ : ℚ, 0 < ξ ∧ ξ < 1 / 100 ∧
      ξ < P.epsilon0 / (2 * k * P.repetitions) := by
  have hdenom : (0 : ℚ) < 2 * k * P.repetitions := by
    exact mul_pos (mul_pos (by norm_num) (by exact_mod_cast hk))
      (by exact_mod_cast P.repetitions_pos)
  let ξ := min (1 / 100 : ℚ) (P.epsilon0 / (2 * k * P.repetitions)) / 2
  have hmin : 0 < min (1 / 100 : ℚ) (P.epsilon0 / (2 * k * P.repetitions)) :=
    lt_min (by norm_num) (div_pos P.epsilon0_pos hdenom)
  refine ⟨ξ, div_pos hmin (by norm_num), ?_, ?_⟩
  · have hle := min_le_left (1 / 100 : ℚ) (P.epsilon0 / (2 * k * P.repetitions))
    dsimp [ξ]
    linarith
  · have hle := min_le_right (1 / 100 : ℚ) (P.epsilon0 / (2 * k * P.repetitions))
    dsimp [ξ]
    linarith

theorem matrix_error_budget (k : ℕ) (hk : 0 < k) (ξ : ℚ)
    (hξ : ξ ≤ P.epsilon0 / (2 * k * P.repetitions)) :
    (k : ℚ) * ξ + P.pStar / 2 ≤ P.epsilon0 / P.repetitions := by
  have hkq : (0 : ℚ) < k := by exact_mod_cast hk
  have htq : (0 : ℚ) < P.repetitions := by exact_mod_cast P.repetitions_pos
  have hx := (le_div_iff₀ (mul_pos (mul_pos (by norm_num) hkq) htq)).mp hξ
  have hp := (le_div_iff₀ htq).mp P.reciprocal_budget
  apply (le_div_iff₀ htq).mpr
  dsimp [pStar]
  nlinarith

end OuterParameters
end
end DFVSGames.ParameterSelection


namespace DFVSGames.Foundations.Complexity.Runtime

def statementPushBound {K : Type} {Γ : K → Type} {Λ σ : Type} :
    Turing.TM2.Stmt Γ Λ σ → Nat
  | .push _ _ next => statementPushBound next + 1
  | .peek _ _ next => statementPushBound next
  | .pop _ _ next => statementPushBound next
  | .load _ next => statementPushBound next
  | .branch _ yes no => max (statementPushBound yes) (statementPushBound no)
  | .goto _ => 0
  | .halt => 0

def maxLabelPushes {K : Type} {Γ : K → Type} {Λ σ : Type}
    (program : Λ → Turing.TM2.Stmt Γ Λ σ) : List Λ → Nat
  | [] => 0
  | label :: rest => max (statementPushBound (program label)) (maxLabelPushes program rest)

theorem maxLabelPushes_ge {K : Type} {Γ : K → Type} {Λ σ : Type}
    (program : Λ → Turing.TM2.Stmt Γ Λ σ) (labels : List Λ) (label : Λ)
    (member : label ∈ labels) :
    statementPushBound (program label) ≤ maxLabelPushes program labels := by
  induction labels with
  | nil => simp at member
  | cons first rest ih =>
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih member) (Nat.le_max_right _ _)

noncomputable def programPushBound (tm : Turing.FinTM2) : Nat :=
  maxLabelPushes tm.m tm.ΛFin.elems.toList

theorem statement_le_programPushBound (tm : Turing.FinTM2) (label : tm.Λ) :
    statementPushBound (tm.m label) ≤ programPushBound tm := by
  apply maxLabelPushes_ge
  simpa using tm.ΛFin.complete label

theorem stepAuxStackLength {K : Type} {Γ : K → Type} {Λ σ : Type} [DecidableEq K]
    (stmt : Turing.TM2.Stmt Γ Λ σ) (state : σ) (tapes : ∀ k, List (Γ k)) (k : K) :
    ((Turing.TM2.stepAux stmt state tapes).stk k).length ≤
      (tapes k).length + statementPushBound stmt := by
  induction stmt generalizing state tapes with
  | push j f next ih =>
      have changed : ((Function.update tapes j (f state :: tapes j)) k).length ≤
          (tapes k).length + 1 := by
        by_cases same : k = j
        · subst k; simp
        · simp [Function.update, same]
      have h := ih state (Function.update tapes j (f state :: tapes j))
      simp only [Turing.TM2.stepAux, statementPushBound]
      omega
  | peek j f next ih =>
      simpa only [Turing.TM2.stepAux, statementPushBound] using
        ih (f state (tapes j).head?) tapes
  | pop j f next ih =>
      have changed : ((Function.update tapes j (tapes j).tail) k).length ≤
          (tapes k).length := by
        by_cases same : k = j
        · subst k; simp
        · simp [Function.update, same]
      have h := ih (f state (tapes j).head?) (Function.update tapes j (tapes j).tail)
      simp only [Turing.TM2.stepAux, statementPushBound]
      omega
  | load f next ih =>
      simpa only [Turing.TM2.stepAux, statementPushBound] using ih (f state) tapes
  | branch condition yes no ihYes ihNo =>
      cases decision : condition state with
      | false =>
          have h := ihNo state tapes
          have hm := Nat.le_max_right (statementPushBound yes) (statementPushBound no)
          simp only [Turing.TM2.stepAux, statementPushBound, decision, Bool.cond_false]
          omega
      | true =>
          have h := ihYes state tapes
          have hm := Nat.le_max_left (statementPushBound yes) (statementPushBound no)
          simp only [Turing.TM2.stepAux, statementPushBound, decision, Bool.cond_true]
          omega
  | goto f => simp [Turing.TM2.stepAux, statementPushBound]
  | halt => simp [Turing.TM2.stepAux, statementPushBound]

private theorem iterateSizeBound_inline_Runtime {α : Type} (f : α → α) (size : α → Nat) (C : Nat)
    (oneStep : ∀ x, size (f x) ≤ size x + C) (n : Nat) (x : α) :
    size ((f^[n]) x) ≤ size x + n * C := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hs := oneStep ((f^[n]) x)
      have bound : size (f ((f^[n]) x)) ≤ size x + (n + 1) * C := by
        rw [Nat.add_mul, Nat.one_mul]
        omega
      simpa only [Function.iterate_succ_apply'] using bound

theorem executionSizeBound {σ : Type} (step : σ → Option σ) (size : σ → Nat) (C : Nat)
    (oneStep : ∀ a b, step a = some b → size b ≤ size a + C)
    {start finish : σ} {budget : Nat}
    (execution : StateTransition.EvalsToInTime step start (some finish) budget) :
    size finish ≤ size start + budget * C := by
  let liftedSize : Option σ → Nat := fun state => (state.map size).getD 0
  have liftedStep : ∀ state : Option σ,
      liftedSize (state.bind step) ≤ liftedSize state + C := by
    intro state
    cases state with
    | none => simp [liftedSize]
    | some a =>
        cases transition : step a with
        | none => simp [liftedSize, transition]
        | some b => simpa [liftedSize, transition] using oneStep a b transition
  have bound := iterateSizeBound_inline_Runtime (fun state : Option σ => state.bind step)
    liftedSize C liftedStep execution.steps (some start)
  change liftedSize ((flip bind step)^[execution.steps] (some start)) ≤ _ at bound
  rw [execution.evals_in_steps] at bound
  simp only [liftedSize, Option.map_some, Option.getD_some] at bound
  exact Nat.le_trans bound (Nat.add_le_add_left
    (Nat.mul_le_mul_right C execution.steps_le_m) _)

theorem stepStackLength (tm : Turing.FinTM2) (k : tm.K) (a b : tm.Cfg)
    (transition : tm.step a = some b) :
    (b.stk k).length ≤ (a.stk k).length + programPushBound tm := by
  cases a with
  | mk label state tapes =>
      cases label with
      | none => simp [Turing.FinTM2.step, Turing.TM2.step] at transition
      | some label =>
          have result := Option.some.inj transition
          rw [← result]
          exact Nat.le_trans (stepAuxStackLength _ _ _ _)
            (Nat.add_le_add_left (statement_le_programPushBound tm label) _)

theorem initialStackLength (tm : Turing.FinTM2) (input : List (tm.Γ tm.k₀)) (k : tm.K) :
    ((Turing.initList tm input).stk k).length ≤ input.length := by
  simp only [Turing.initList]
  split
  next same => subst k; exact Nat.le_refl _
  next _ => simp

@[simp] theorem haltedOutputLength (tm : Turing.FinTM2) (output : List (tm.Γ tm.k₁)) :
    ((Turing.haltList tm output).stk tm.k₁).length = output.length := by
  simp [Turing.haltList]

theorem outputLength_le (tm : Turing.FinTM2) (input : List (tm.Γ tm.k₀))
    (output : List (tm.Γ tm.k₁)) (budget : Nat)
    (execution : Turing.TM2OutputsInTime tm input (some output) budget) :
    output.length ≤ input.length + budget * programPushBound tm := by
  have bound := executionSizeBound tm.step (fun cfg => (cfg.stk tm.k₁).length)
    (programPushBound tm) (stepStackLength tm tm.k₁) execution
  calc
    output.length = ((Turing.haltList tm output).stk tm.k₁).length := (haltedOutputLength tm output).symm
    _ ≤ ((Turing.initList tm input).stk tm.k₁).length + budget * programPushBound tm := bound
    _ ≤ input.length + budget * programPushBound tm :=
      Nat.add_le_add_right (initialStackLength tm input tm.k₁) _

theorem encodedOutputLength {α β αΓ βΓ : Type}
    {ea : α → List αΓ} {eb : β → List βΓ} {f : α → β}
    (certificate : Turing.TM2ComputableInPolyTime ea eb f) (a : α) :
    (eb (f a)).length ≤
      (Polynomial.X + Polynomial.C (programPushBound certificate.tm) * certificate.time).eval
        (ea a).length := by
  have bound := outputLength_le certificate.tm _ _ _ (certificate.outputsFun a)
  simpa only [List.length_map, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_mul, Polynomial.eval_C, Nat.mul_comm] using bound

end DFVSGames.Foundations.Complexity.Runtime

end OAI
