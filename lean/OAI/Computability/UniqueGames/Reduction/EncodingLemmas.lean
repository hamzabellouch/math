import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.OfMap
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Logic.Equiv.Fin.Basic
import OAI.Computability.UniqueGames.Foundations.PinskerLemmas
import OAI.Computability.UniqueGames.Machines.MachineSubroutineLemmas
import OAI.Computability.UniqueGames.Reduction.ActualCanonicalLemmas
import OAI.Computability.UniqueGames.Reduction.BinaryLinear

namespace OAI

section

/-! Computable binary alphabet indexing and full translation permutation tables.
The labels are actual `Fin (2^s)` entries in the target instance format.
-/

namespace UniqueGamesTheorem.Reduction.Encoding

open Integration.BinaryLinear
open Foundations.Target

/-- Number the left side first and the right side second. -/
def sideEquiv (n : Nat) : Bool × Fin n ≃ Fin (2*n) :=
  (finTwoEquiv.symm.prodCongr (Equiv.refl (Fin n))).trans finProdFinEquiv

@[simp] theorem sideEquiv_false_val {count : Nat} (i : Fin count) :
    (sideEquiv count (false, i)).val = i.val := by
  simp [sideEquiv, finProdFinEquiv, finTwoEquiv]

@[simp] theorem sideEquiv_true_val {count : Nat} (i : Fin count) :
    (sideEquiv count (true, i)).val = count + i.val := by
  simp [sideEquiv, finProdFinEquiv, finTwoEquiv, Nat.add_comm]

/-- The integer label is the packed, least-significant-bit-first coordinate word. -/
def alphabetEquiv (s : Nat) : Integration.BinaryLinear.Vector s ≃ Fin (2^s) :=
  (coordinatesEquiv s).symm.trans
    { toFun := BitVec.toFin
      invFun := BitVec.ofFin
      left_inv := BitVec.ofFin_toFin
      right_inv := BitVec.toFin_ofFin }

@[simp] theorem alphabetEquiv_symm_apply_apply (s : Nat)
    (c : Integration.BinaryLinear.Vector s) :
    (alphabetEquiv s).symm (alphabetEquiv s c) = c :=
  (alphabetEquiv s).symm_apply_apply c

@[simp] theorem alphabetEquiv_apply_symm_apply (s : Nat) (c : Fin (2^s)) :
    alphabetEquiv s ((alphabetEquiv s).symm c) = c :=
  (alphabetEquiv s).apply_symm_apply c

def translate {s : Nat} (a b : Integration.BinaryLinear.Vector s)
    (c : Fin (2^s)) : Fin (2^s) :=
  alphabetEquiv s ((alphabetEquiv s).symm c + a + b)

theorem translate_involutive {s : Nat} (a b : Integration.BinaryLinear.Vector s) :
    Function.Involutive (translate a b) := by
  intro c
  simp only [translate, alphabetEquiv_symm_apply_apply]
  have h : (alphabetEquiv s).symm c + a + b + a + b = (alphabetEquiv s).symm c := by
    ext i
    simp only [Pi.add_apply]
    rw [show (alphabetEquiv s).symm c i + a i + b i + a i + b i =
      (alphabetEquiv s).symm c i + (a i + a i) + (b i + b i) by abel]
    simp [CharTwo.add_self_eq_zero]
  rw [h, alphabetEquiv_apply_symm_apply]

/-- Both forward and inverse tables are explicitly generated from every alphabet
index. Characteristic two makes these two tables equal. -/
def translationTable {s : Nat} (a b : Integration.BinaryLinear.Vector s) :
    PermutationTable (2^s) where
  images := _root_.Vector.ofFn (translate a b)
  inverseImages := _root_.Vector.ofFn (translate a b)
  leftInverse c := by simpa using translate_involutive a b c
  rightInverse c := by simpa using translate_involutive a b c

@[simp] theorem translationTable_images {s : Nat}
    (a b c : Integration.BinaryLinear.Vector s) :
    (translationTable a b).images[alphabetEquiv s c] = alphabetEquiv s (c + a + b) := by
  simp [translationTable, translate]

@[simp] theorem translationTable_inverseImages {s : Nat}
    (a b c : Integration.BinaryLinear.Vector s) :
    (translationTable a b).inverseImages[alphabetEquiv s c] =
      alphabetEquiv s (c + a + b) := by
  simp [translationTable, translate]

theorem translationTable_satisfied_iff {s : Nat}
    (a b cLeft cRight : Integration.BinaryLinear.Vector s) :
    (translationTable a b).images[alphabetEquiv s cLeft] = alphabetEquiv s cRight ↔
      cLeft + a + b = cRight := by
  rw [translationTable_images]
  exact (alphabetEquiv s).injective.eq_iff

section ImageNumbering

variable {Q V : Type*} [DecidableEq V]

/-- Canonical vertex bodies are compared using their actual decidable equality.
`List.dedup` fixes a deterministic order by retaining the last occurrence. -/
def imageVertices (queries : List Q) (body : Q → V) : List V :=
  (queries.map body).dedup

theorem mem_imageVertices {queries : List Q} {body : Q → V} {v : V} :
    v ∈ imageVertices queries body ↔ ∃ q ∈ queries, body q = v := by
  simp [imageVertices]

theorem imageVertices_nodup (queries : List Q) (body : Q → V) :
    (imageVertices queries body).Nodup := List.nodup_dedup _

theorem imageVertices_length_le (queries : List Q) (body : Q → V) :
    (imageVertices queries body).length ≤ queries.length := by
  simpa only [imageVertices, List.length_map] using
    (List.dedup_sublist (queries.map body)).length_le

abbrev ImageVertex (queries : List Q) (body : Q → V) :=
  {v : V // v ∈ imageVertices queries body}

/-- A computable numbering using `idxOf`; its inverse looks up that index.
It involves no chosen `Fintype.equivFin`. -/
def imageEquiv (queries : List Q) (body : Q → V) :
    ImageVertex queries body ≃ Fin (imageVertices queries body).length :=
  (List.Nodup.getEquiv _ (imageVertices_nodup queries body)).symm

def imageVertex (queries : List Q) (body : Q → V) (q : Q) (hq : q ∈ queries) :
    ImageVertex queries body := ⟨body q, mem_imageVertices.mpr ⟨q, hq, rfl⟩⟩

def imageIndex (queries : List Q) (body : Q → V) (q : Q) (hq : q ∈ queries) :
    Fin (imageVertices queries body).length := imageEquiv queries body (imageVertex queries body q hq)

theorem imageIndex_eq_iff (queries : List Q) (body : Q → V)
    (q r : Q) (hq : q ∈ queries) (hr : r ∈ queries) :
    imageIndex queries body q hq = imageIndex queries body r hr ↔ body q = body r := by
  simp only [imageIndex, (imageEquiv queries body).injective.eq_iff, Subtype.mk.injEq,
    imageVertex]

theorem imageVertices_range (queries : List Q) (body : Q → V)
    (full : ∀ q, q ∈ queries) (v : V) :
    v ∈ imageVertices queries body ↔ v ∈ Set.range body := by
  simp [mem_imageVertices, full, Set.mem_range]

end ImageNumbering

end UniqueGamesTheorem.Reduction.Encoding

end

section

/-! The finite set of realizable orbit records.  Vertices are the image of the
actual canonical-data map, so equal retained data from different questions
become one vertex.  The two sides remain distinct. -/

namespace UniqueGamesTheorem.Reduction.ActualOrbit

open UniqueGamesTheorem.Integration.BinaryLinear

universe u v

variable {Q : Type u} {T : Type v} {s d : Nat}

abbrev Ambient (s d : Nat) := Vector s × Vector d

def body (can : Q → Ambient s d × T) (q : Q) : Vector d × T :=
  ((can q).1.2, (can q).2)

def offset (can : Q → Ambient s d × T) (q : Q) : Vector s := (can q).1.1

/-- Only realized bodies are vertices; no extra formal records are added. -/
def Vertex (can : Q → Ambient s d × T) := {o : Vector d × T // ∃ q, body can q = o}

def vertex (can : Q → Ambient s d × T) (q : Q) : Vertex can :=
  ⟨body can q, q, rfl⟩

theorem vertex_surjective (can : Q → Ambient s d × T) :
    Function.Surjective (vertex can) := by
  rintro ⟨o, q, hq⟩
  exact ⟨q, Subtype.ext hq⟩

noncomputable instance vertexFintype [Fintype Q] (can : Q → Ambient s d × T) :
    Fintype (Vertex can) := by
  classical
  exact Fintype.ofSurjective (vertex can) (vertex_surjective can)

instance vertexNonempty [Nonempty Q] (can : Q → Ambient s d × T) :
    Nonempty (Vertex can) := Nonempty.map (vertex can) inferInstance

theorem vertex_eq_iff (can : Q → Ambient s d × T) (q r : Q) :
    vertex can q = vertex can r ↔ body can q = body can r := by
  constructor
  · exact congrArg Subtype.val
  · intro h
    exact Subtype.ext h

/-- `false` is the left copy and `true` is the right copy. -/
abbrev TwoSidedVertex (can : Q → Ambient s d × T) := Bool × Vertex can

noncomputable def vertexEquiv [Fintype Q] (can : Q → Ambient s d × T) :
    TwoSidedVertex can ≃ Fin (Fintype.card (TwoSidedVertex can)) :=
  Fintype.equivFin _

/-- Executable vertex numbering from an exhaustive list, preserving the same
realizable-body subtype used in the semantic statements. -/
def explicitVertexEquiv [DecidableEq (Vector d × T)]
    (can : Q → Ambient s d × T) (queries : List Q) (full : ∀ q, q ∈ queries) :
    Vertex can ≃ Fin (Encoding.imageVertices queries (body can)).length :=
  let e : Vertex can ≃ Encoding.ImageVertex queries (body can) :=
    { toFun v := ⟨v.val, (Encoding.imageVertices_range queries (body can) full v.val).mpr
        v.property⟩
      invFun v := ⟨v.val, (Encoding.imageVertices_range queries (body can) full v.val).mp
        v.property⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  e.trans (Encoding.imageEquiv queries (body can))

def unfold (can : Q → Ambient s d × T) (label : Vertex can → Vector s) (q : Q) :
    Vector s := label (vertex can q) + offset can q

theorem add_self_vector (c : Vector s) : c + c = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero (c i)

theorem add_cancel_vector (a b : Vector s) : (a + b) + b = a := by
  rw [add_assoc, add_self_vector, add_zero]

/-- The precise orientation used by the generated edge. -/
theorem constraint_iff_unfolded (can : Q → Ambient s d × T)
    (labelL labelR : Vertex can → Vector s) (q r : Q) :
    (labelL (vertex can q) + offset can q) + offset can r = labelR (vertex can r) ↔
      unfold can labelL q = unfold can labelR r := by
  constructor
  · intro h
    have h' := congrArg (fun c => c + offset can r) h
    simpa only [add_cancel_vector, unfold] using h'
  · intro h
    have h' := congrArg (fun c => c + offset can r) h
    simpa only [add_cancel_vector, unfold] using h'

/-- A common full canonical record has one common unfolded value on each side. -/
theorem unfold_eq_of_canonical_eq (can : Q → Ambient s d × T)
    (label : Vertex can → Vector s) (q r : Q) (h : can q = can r) :
    unfold can label q = unfold can label r := by
  have hv : vertex can q = vertex can r := by
    apply (vertex_eq_iff can q r).2
    exact congrArg (fun z : Ambient s d × T => (z.1.2, z.2)) h
  simp only [unfold, hv, offset, h]

end UniqueGamesTheorem.Reduction.ActualOrbit

end

section

/-! Internal serialization of canonical orbit bodies. Each record occupies nine
natural-number words, so record boundaries are independent of the tag. The
outer complement coordinate occupies one leading word. These are injectivity,
deduplication, and output-size statements, not machine running-time claims. -/

namespace UniqueGamesTheorem.Reduction.CanonicalEncoding

open Integration.BinaryLinear
open Foundations.Complexity

abbrev Ambient (s d : Nat) := Integration.BinaryLinear.Vector s × Integration.BinaryLinear.Vector d
abbrev Record (n m s d : Nat) := ActualCanonical.Record (Fin n) (Fin m) (Ambient s d)
abbrev Body (n m k s d : Nat) := Integration.BinaryLinear.Vector d × (Fin k → Record n m s d)

def vectorWord {s : Nat} (v : Integration.BinaryLinear.Vector s) : Nat :=
  (Encoding.alphabetEquiv s v).val

theorem vectorWord_lt {s : Nat} (v : Integration.BinaryLinear.Vector s) :
    vectorWord v < 2^s := (Encoding.alphabetEquiv s v).isLt

theorem vectorWord_injective {s : Nat} :
    Function.Injective (vectorWord (s := s)) := by
  intro x y h
  apply (Encoding.alphabetEquiv s).injective
  exact Fin.ext h

@[simp] theorem vectorWord_eq_iff {s : Nat} (x y : Integration.BinaryLinear.Vector s) :
    vectorWord x = vectorWord y ↔ x = y := vectorWord_injective.eq_iff

/-- Words: tag, name, occurrence, followed by three split coefficient pairs.
Padding is zero. A single record uses only the first coefficient pair. -/
def recordWords {n m s d : Nat} : Record n m s d → List Nat
  | .blank => [0, 0, 0, 0, 0, 0, 0, 0, 0]
  | .single name coefficient =>
      [1, name.val, 0, vectorWord coefficient.1, vectorWord coefficient.2, 0, 0, 0, 0]
  | .full occurrence coefficients =>
      [2, 0, occurrence.val,
        vectorWord (coefficients 0).1, vectorWord (coefficients 0).2,
        vectorWord (coefficients 1).1, vectorWord (coefficients 1).2,
        vectorWord (coefficients 2).1, vectorWord (coefficients 2).2]

@[simp] theorem recordWords_length {n m s d : Nat} (r : Record n m s d) :
    (recordWords r).length = 9 := by
  cases r <;> rfl

theorem recordWords_injective {n m s d : Nat} :
    Function.Injective (recordWords (n := n) (m := m) (s := s) (d := d)) := by
  intro r t h
  cases r with
  | blank => cases t <;> simp_all [recordWords]
  | single name coefficient =>
    cases t with
    | blank => simp [recordWords] at h
    | single name' coefficient' =>
      simp [recordWords] at h
      rcases h with ⟨hn, hc, hd⟩
      have hp : coefficient = coefficient' := Prod.ext hc hd
      have hn' : name = name' := Fin.ext hn
      cases hn'
      cases hp
      rfl
    | full occurrence coefficients => simp [recordWords] at h
  | full occurrence coefficients =>
    cases t with
    | blank => simp [recordWords] at h
    | single name coefficient => simp [recordWords] at h
    | full occurrence' coefficients' =>
      simp [recordWords] at h
      rcases h with ⟨hi, h0c, h0d, h1c, h1d, h2c, h2d⟩
      have hp : coefficients = coefficients' := by
        funext i
        fin_cases i
        · exact Prod.ext h0c h0d
        · exact Prod.ext h1c h1d
        · exact Prod.ext h2c h2d
      have hi' : occurrence = occurrence' := Fin.ext hi
      cases hi'
      cases hp
      rfl

def recordsWords {n m s d : Nat} (rs : List (Record n m s d)) : List Nat :=
  rs.flatMap recordWords

@[simp] theorem recordsWords_nil {n m s d : Nat} :
    recordsWords ([] : List (Record n m s d)) = [] := rfl

@[simp] theorem recordsWords_cons {n m s d : Nat} (r : Record n m s d)
    (rs : List (Record n m s d)) :
    recordsWords (r :: rs) = recordWords r ++ recordsWords rs := rfl

@[simp] theorem recordsWords_length {n m s d : Nat} (rs : List (Record n m s d)) :
    (recordsWords rs).length = 9 * rs.length := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp [ih, Nat.mul_add, Nat.add_comm]

theorem recordsWords_take_head {n m s d : Nat} (r : Record n m s d)
    (rs : List (Record n m s d)) :
    (recordsWords (r :: rs)).take 9 = recordWords r := by
  change (recordWords r ++ recordsWords rs).take 9 = recordWords r
  simpa only [recordWords_length] using
    (List.take_append_length (l₁ := recordWords r) (l₂ := recordsWords rs))

theorem recordsWords_injective {n m s d : Nat} :
    Function.Injective (recordsWords (n := n) (m := m) (s := s) (d := d)) := by
  intro rs
  induction rs with
  | nil =>
    intro ts h
    cases ts with
    | nil => rfl
    | cons t ts =>
      have hl := congrArg List.length h
      simp only [recordsWords_length, List.length_nil, List.length_cons] at hl
      omega
  | cons r rs ih =>
    intro ts h
    cases ts with
    | nil =>
      have hl := congrArg List.length h
      simp only [recordsWords_length, List.length_nil, List.length_cons] at hl
      omega
    | cons t ts =>
      have hh := congrArg (List.take 9) h
      simp only [recordsWords_take_head] at hh
      have hr := recordWords_injective hh
      subst t
      apply congrArg (List.cons r)
      apply ih
      exact List.append_cancel_left (by simpa only [recordsWords_cons] using h)

def bodyWords {n m k s d : Nat} (body : Body n m k s d) : List Nat :=
  vectorWord body.1 :: recordsWords (List.ofFn body.2)

@[simp] theorem bodyWords_length {n m k s d : Nat} (body : Body n m k s d) :
    (bodyWords body).length = 1 + 9*k := by
  simp [bodyWords, Nat.add_comm]

theorem bodyWords_injective {n m k s d : Nat} :
    Function.Injective (bodyWords (n := n) (m := m) (k := k) (s := s) (d := d)) := by
  intro x y h
  have hh := List.cons.inj h
  apply Prod.ext
  · exact vectorWord_injective hh.1
  · exact List.ofFn_injective (recordsWords_injective hh.2)

@[simp] theorem bodyWords_eq_iff {n m k s d : Nat} (x y : Body n m k s d) :
    bodyWords x = bodyWords y ↔ x = y := bodyWords_injective.eq_iff

def wordBound (n m s d : Nat) : Nat := n + m + 2^s + 2^d + 3

theorem recordWords_bounded {n m s d : Nat} (r : Record n m s d)
    (w : Nat) (hw : w ∈ recordWords r) : w ≤ wordBound n m s d := by
  unfold wordBound
  cases r with
  | blank =>
    simp [recordWords] at hw
    subst w
    exact Nat.zero_le _
  | single name coefficient =>
    have hn := name.isLt
    have hc := vectorWord_lt coefficient.1
    have hd := vectorWord_lt coefficient.2
    simp only [recordWords, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with h | h | h | h | h | h | h | h | h <;> omega
  | full occurrence coefficients =>
    have hi := occurrence.isLt
    have h0c := vectorWord_lt (coefficients 0).1
    have h0d := vectorWord_lt (coefficients 0).2
    have h1c := vectorWord_lt (coefficients 1).1
    have h1d := vectorWord_lt (coefficients 1).2
    have h2c := vectorWord_lt (coefficients 2).1
    have h2d := vectorWord_lt (coefficients 2).2
    simp only [recordWords, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with h | h | h | h | h | h | h | h | h <;> omega

theorem bodyWords_bounded {n m k s d : Nat} (body : Body n m k s d)
    (w : Nat) (hw : w ∈ bodyWords body) : w ≤ wordBound n m s d := by
  rcases List.mem_cons.mp hw with h | h
  · subst w
    have hv := vectorWord_lt body.1
    have hs : 0 < (2 : Nat)^s := pow_pos (by decide) _
    unfold wordBound
    omega
  · obtain ⟨r, _, hr⟩ := List.mem_flatMap.mp h
    exact recordWords_bounded r w hr

def bodyBits {n m k s d : Nat} (body : Body n m k s d) : List Bool :=
  encodeWords (bodyWords body)

theorem bodyBits_injective {n m k s d : Nat} :
    Function.Injective (bodyBits (n := n) (m := m) (k := k) (s := s) (d := d)) := by
  intro x y h
  exact bodyWords_injective (encodeWords_injective h)

@[simp] theorem bodyBits_eq_iff {n m k s d : Nat} (x y : Body n m k s d) :
    bodyBits x = bodyBits y ↔ x = y := bodyBits_injective.eq_iff

theorem bodyBits_length_le {n m k s d : Nat} (body : Body n m k s d) :
    (bodyBits body).length ≤ (1 + 9*k) * (n + m + 2^s + 2^d + 4) := by
  simpa only [bodyBits, bodyWords_length, wordBound, Nat.add_assoc] using
    encodeWords_length_le (bodyWords body) (wordBound n m s d) (bodyWords_bounded body)

/-- Serializing before deduplication preserves the exact retained vertex order. -/
theorem imageVertices_bodyWords {Q : Type*} {n m k s d : Nat}
    [DecidableEq (Body n m k s d)] (queries : List Q) (body : Q → Body n m k s d) :
    Encoding.imageVertices queries (fun q => bodyWords (body q)) =
      (Encoding.imageVertices queries body).map bodyWords := by
  unfold Encoding.imageVertices
  simpa only [List.map_map, Function.comp_def] using
    List.dedup_map_of_injective bodyWords_injective (queries.map body)

theorem imageVertices_bodyBits {Q : Type*} {n m k s d : Nat}
    [DecidableEq (Body n m k s d)] (queries : List Q) (body : Q → Body n m k s d) :
    Encoding.imageVertices queries (fun q => bodyBits (body q)) =
      (Encoding.imageVertices queries body).map bodyBits := by
  unfold Encoding.imageVertices
  simpa only [List.map_map, Function.comp_def] using
    List.dedup_map_of_injective bodyBits_injective (queries.map body)

theorem idxOf_map_injective {A B : Type*} [DecidableEq A] [DecidableEq B]
    (f : A → B) (hf : Function.Injective f) (x : A) (xs : List A) :
    (xs.map f).idxOf (f x) = xs.idxOf x := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    by_cases h : y = x
    · subst y
      simp
    · have h' : f y ≠ f x := fun hxy => h (hf hxy)
      simp [h, h', ih]

/-- Injective serialization leaves the actual numeric vertex index unchanged,
not just the vertex set or its cardinality. -/
theorem imageIndex_map_val {Q A B : Type*} [DecidableEq A] [DecidableEq B]
    (queries : List Q) (body : Q → A) (f : A → B) (hf : Function.Injective f)
    (q : Q) (hq : q ∈ queries) :
    (Encoding.imageIndex queries (fun q => f (body q)) q hq).val =
      (Encoding.imageIndex queries body q hq).val := by
  change ((queries.map (fun q => f (body q))).dedup).idxOf (f (body q)) =
    ((queries.map body).dedup).idxOf (body q)
  have hmap : (queries.map (fun q => f (body q))).dedup =
      (queries.map body).dedup.map f := by
    simpa only [List.map_map, Function.comp_def] using
      List.dedup_map_of_injective hf (queries.map body)
  rw [hmap]
  exact idxOf_map_injective f hf (body q) (queries.map body).dedup

theorem imageIndex_bodyWords_val {Q : Type*} {n m k s d : Nat}
    [DecidableEq (Body n m k s d)] (queries : List Q) (body : Q → Body n m k s d)
    (q : Q) (hq : q ∈ queries) :
    (Encoding.imageIndex queries (fun q => bodyWords (body q)) q hq).val =
      (Encoding.imageIndex queries body q hq).val :=
  imageIndex_map_val queries body bodyWords bodyWords_injective q hq

theorem imageIndex_bodyBits_val {Q : Type*} {n m k s d : Nat}
    [DecidableEq (Body n m k s d)] (queries : List Q) (body : Q → Body n m k s d)
    (q : Q) (hq : q ∈ queries) :
    (Encoding.imageIndex queries (fun q => bodyBits (body q)) q hq).val =
      (Encoding.imageIndex queries body q hq).val :=
  imageIndex_map_val queries body bodyBits bodyBits_injective q hq

end UniqueGamesTheorem.Reduction.CanonicalEncoding

end

section

/-! Direct canonical-body addresses. The fixed list of canonical words is
interpreted in big-endian order, matching forward Horner steps `B*acc+digit`.
Unused addresses represent isolated vertices. These are semantic encoding and
polynomial-size results, not an assumed machine implementation. -/

namespace UniqueGamesTheorem.Reduction.CanonicalAddress

open CanonicalEncoding

/-- Most-significant-word first, with leading zero words retained in the
fixed-length domain. Mathlib's `ofDigits` uses the opposite list order. -/
def radix (B : Nat) (words : List Nat) : Nat := Nat.ofDigits B words.reverse

theorem radix_eq_foldl (B : Nat) (words : List Nat) :
    radix B words = words.foldl (fun acc digit => B * acc + digit) 0 := by
  unfold radix
  rw [Nat.ofDigits_eq_foldr, List.foldr_reverse]
  simp only [Nat.cast_id, Nat.add_comm]

@[simp] theorem radix_nil (B : Nat) : radix B [] = 0 := rfl

/-- This is precisely the arithmetic operation of `MachineRadixStep`. -/
theorem radix_append_word (B : Nat) (words : List Nat) (digit : Nat) :
    radix B (words ++ [digit]) = B * radix B words + digit := by
  simp only [radix_eq_foldl, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem radix_lt_pow_length {B : Nat} (hB : 1 < B) (words : List Nat)
    (bounded : ∀ w ∈ words, w < B) : radix B words < B ^ words.length := by
  unfold radix
  simpa only [List.length_reverse] using
    Nat.ofDigits_lt_base_pow_length hB
      (fun w hw => bounded w (List.mem_reverse.mp hw))

/-- Fixed width makes leading zero words unambiguous. -/
theorem radix_injective_of_length_eq {B : Nat} (hB : 1 < B)
    {xs ys : List Nat} (sameLength : xs.length = ys.length)
    (xsBounded : ∀ w ∈ xs, w < B) (ysBounded : ∀ w ∈ ys, w < B)
    (sameAddress : radix B xs = radix B ys) : xs = ys := by
  have reversed : xs.reverse = ys.reverse :=
    Nat.ofDigits_inj_of_len_eq hB (by simpa only [List.length_reverse] using sameLength)
      (fun w hw => xsBounded w (List.mem_reverse.mp hw))
      (fun w hw => ysBounded w (List.mem_reverse.mp hw)) sameAddress
  have h := congrArg List.reverse reversed
  simpa only [List.reverse_reverse] using h

/-- One larger than the proved bound on every canonical word. -/
def base (n m s d : Nat) : Nat := wordBound n m s d + 1

@[simp] theorem base_eq (n m s d : Nat) :
    base n m s d = n + m + 2^s + 2^d + 4 := by
  simp [base, wordBound, Nat.add_assoc]

theorem one_lt_base (n m s d : Nat) : 1 < base n m s d := by
  have h : 3 ≤ wordBound n m s d := by
    unfold wordBound
    exact Nat.le_add_left 3 _
  unfold base
  omega

theorem bodyWords_lt_base {n m k s d : Nat} (body : Body n m k s d)
    (w : Nat) (hw : w ∈ bodyWords body) : w < base n m s d :=
  Nat.lt_succ_of_le (bodyWords_bounded body w hw)

def capacity (n m k s d : Nat) : Nat := (base n m s d) ^ (1 + 9*k)

theorem capacity_pos (n m k s d : Nat) : 0 < capacity n m k s d :=
  pow_pos (Nat.zero_lt_of_lt (one_lt_base n m s d)) _

def bodyAddress {n m k s d : Nat} (body : Body n m k s d) :
    Fin (capacity n m k s d) :=
  ⟨radix (base n m s d) (bodyWords body), by
    simpa only [capacity, bodyWords_length] using
      radix_lt_pow_length (one_lt_base n m s d) (bodyWords body) (bodyWords_lt_base body)⟩

@[simp] theorem bodyAddress_val {n m k s d : Nat} (body : Body n m k s d) :
    (bodyAddress body).val = radix (base n m s d) (bodyWords body) := rfl

theorem bodyAddress_injective {n m k s d : Nat} :
    Function.Injective (bodyAddress (n := n) (m := m) (k := k) (s := s) (d := d)) := by
  intro x y h
  apply bodyWords_injective
  exact radix_injective_of_length_eq (one_lt_base n m s d)
    (by simp only [bodyWords_length]) (bodyWords_lt_base x) (bodyWords_lt_base y)
    (congrArg Fin.val h)

@[simp] theorem bodyAddress_eq_iff {n m k s d : Nat} (x y : Body n m k s d) :
    bodyAddress x = bodyAddress y ↔ x = y := bodyAddress_injective.eq_iff

/-- For fixed k,s,d, the entire direct-address space is a polynomial in n+m. -/
noncomputable def capacityPolynomial (k s d : Nat) : Polynomial Nat :=
  (Polynomial.X + Polynomial.C (2^s + 2^d + 4)) ^ (1 + 9*k)

theorem capacityPolynomial_eval (n m k s d : Nat) :
    (capacityPolynomial k s d).eval (n + m) = capacity n m k s d := by
  simp [capacityPolynomial, capacity, base_eq, Nat.add_assoc]

end UniqueGamesTheorem.Reduction.CanonicalAddress

end

section

namespace UniqueGamesTheorem.Reduction.CanonicalWordTemplate

open Foundations.Complexity CanonicalEncoding

/-- A literal word or a reference to one of the four saved input fields. -/
inductive Token
  | literal (value : Nat)
  | name (index : Fin 3)
  | occurrence
  deriving DecidableEq, Repr

def evalToken (names : Fin 3 → Nat) (occurrence : Nat) : Token → Nat
  | .literal value => value
  | .name index => names index
  | .occurrence => occurrence

def evalTemplate (names : Fin 3 → Nat) (occurrence : Nat)
    (tokens : List Token) : List Nat :=
  tokens.map (evalToken names occurrence)

def isVariable : Token → Bool
  | .literal _ => false
  | .name _ => true
  | .occurrence => true

def variableTokens (tokens : List Token) : List Token := tokens.filter isVariable

def blankTemplate : List Token :=
  [.literal 0, .literal 0, .literal 0, .literal 0, .literal 0,
    .literal 0, .literal 0, .literal 0, .literal 0]

def singleTemplate {s d : Nat} (index : Fin 3) (coefficient : Ambient s d) : List Token :=
  [.literal 1, .name index, .literal 0,
    .literal (vectorWord coefficient.1), .literal (vectorWord coefficient.2),
    .literal 0, .literal 0, .literal 0, .literal 0]

def fullTemplate {s d : Nat} (coefficients : Fin 3 → Ambient s d) : List Token :=
  [.literal 2, .literal 0, .occurrence,
    .literal (vectorWord (coefficients 0).1), .literal (vectorWord (coefficients 0).2),
    .literal (vectorWord (coefficients 1).1), .literal (vectorWord (coefficients 1).2),
    .literal (vectorWord (coefficients 2).1), .literal (vectorWord (coefficients 2).2)]

/-- Coefficient equality alone selects the record tag and the input field. -/
def template {s d : Nat} (a : Fin 3 → Ambient s d) : List Token :=
  if a 0 = a 1 then
    if a 0 = a 2 then blankTemplate else singleTemplate 2 (a 2 + a 0)
  else if a 0 = a 2 then singleTemplate 1 (a 1 + a 0)
  else if a 1 = a 2 then singleTemplate 0 (a 0 + a 2)
  else fullTemplate (ActualCanonical.normalize a)

@[simp] theorem blankTemplate_length : blankTemplate.length = 9 := rfl

@[simp] theorem singleTemplate_length {s d : Nat} (index : Fin 3)
    (coefficient : Ambient s d) : (singleTemplate index coefficient).length = 9 := rfl

@[simp] theorem fullTemplate_length {s d : Nat} (coefficients : Fin 3 → Ambient s d) :
    (fullTemplate coefficients).length = 9 := rfl

@[simp] theorem template_length {s d : Nat} (a : Fin 3 → Ambient s d) :
    (template a).length = 9 := by
  unfold template
  split_ifs <;> rfl

@[simp] theorem evalTemplate_length (names : Fin 3 → Nat) (occurrence : Nat)
    (tokens : List Token) : (evalTemplate names occurrence tokens).length = tokens.length :=
  List.length_map _

theorem eval_blankTemplate {n m s d : Nat} (names : Fin 3 → Fin n) (occurrence : Fin m) :
    evalTemplate (fun j => (names j).val) occurrence.val blankTemplate =
      recordWords (ActualCanonical.Record.blank : Record n m s d) := rfl

theorem eval_singleTemplate {n m s d : Nat} (names : Fin 3 → Fin n) (occurrence : Fin m)
    (index : Fin 3) (coefficient : Ambient s d) :
    evalTemplate (fun j => (names j).val) occurrence.val (singleTemplate index coefficient) =
      recordWords (ActualCanonical.Record.single (names index) coefficient : Record n m s d) :=
  rfl

theorem eval_fullTemplate {n m s d : Nat} (names : Fin 3 → Fin n) (occurrence : Fin m)
    (coefficients : Fin 3 → Ambient s d) :
    evalTemplate (fun j => (names j).val) occurrence.val (fullTemplate coefficients) =
      recordWords (ActualCanonical.Record.full occurrence coefficients : Record n m s d) :=
  rfl

/-- The template evaluates to the exact existing canonical-record encoding. -/
theorem eval_template {n m s d : Nat} (names : Fin m → Fin 3 → Fin n)
    (occurrence : Fin m) (a : Fin 3 → Ambient s d) :
    evalTemplate (fun j => (names occurrence j).val) occurrence.val (template a) =
      recordWords (ActualCanonical.record names occurrence a) := by
  unfold template ActualCanonical.record
  split_ifs <;> rfl

@[simp] theorem variableTokens_blankTemplate : variableTokens blankTemplate = [] := rfl

@[simp] theorem variableTokens_singleTemplate {s d : Nat} (index : Fin 3)
    (coefficient : Ambient s d) :
    variableTokens (singleTemplate index coefficient) = [.name index] := rfl

@[simp] theorem variableTokens_fullTemplate {s d : Nat}
    (coefficients : Fin 3 → Ambient s d) :
    variableTokens (fullTemplate coefficients) = [.occurrence] := rfl

/-- Exact input-field profile: blank has none; single reads one selected name;
full reads the occurrence identifier. Coefficient values are program constants. -/
theorem variableTokens_template {s d : Nat} (a : Fin 3 → Ambient s d) :
    variableTokens (template a) =
      if a 0 = a 1 then
        if a 0 = a 2 then [] else [.name 2]
      else if a 0 = a 2 then [.name 1]
      else if a 1 = a 2 then [.name 0]
      else [.occurrence] := by
  unfold template
  split_ifs <;> rfl

theorem variableTokens_template_length_le_one {s d : Nat} (a : Fin 3 → Ambient s d) :
    (variableTokens (template a)).length ≤ 1 := by
  rw [variableTokens_template]
  split_ifs <;> simp

theorem name_mem_variableTokens_iff {s d : Nat} (a : Fin 3 → Ambient s d) (index : Fin 3) :
    Token.name index ∈ variableTokens (template a) ↔
      (a 0 = a 1 ∧ a 0 ≠ a 2 ∧ index = 2) ∨
      (a 0 ≠ a 1 ∧ a 0 = a 2 ∧ index = 1) ∨
      (a 0 ≠ a 1 ∧ a 0 ≠ a 2 ∧ a 1 = a 2 ∧ index = 0) := by
  by_cases h01 : a 0 = a 1 <;> by_cases h02 : a 0 = a 2 <;>
    by_cases h12 : a 1 = a 2 <;> simp [variableTokens_template, h01, h02, h12]

theorem occurrence_mem_variableTokens_iff {s d : Nat} (a : Fin 3 → Ambient s d) :
    Token.occurrence ∈ variableTokens (template a) ↔
      a 0 ≠ a 1 ∧ a 0 ≠ a 2 ∧ a 1 ≠ a 2 := by
  by_cases h01 : a 0 = a 1 <;> by_cases h02 : a 0 = a 2 <;>
    by_cases h12 : a 1 = a 2 <;> simp [variableTokens_template, h01, h02, h12]

/-- Emitting each token's existing unary-delimited word gives exactly the
existing list-of-words serialization, with no alternative encoding. -/
theorem flatMap_encodeWord (names : Fin 3 → Nat) (occurrence : Nat) (tokens : List Token) :
    tokens.flatMap (fun token => encodeWord (evalToken names occurrence token)) =
      encodeWords (evalTemplate names occurrence tokens) := by
  induction tokens with
  | nil => rfl
  | cons token tokens ih =>
    simp only [List.flatMap_cons, evalTemplate, List.map_cons, encodeWords]
    exact congrArg (List.append (encodeWord (evalToken names occurrence token))) ih

theorem template_bits {n m s d : Nat} (names : Fin m → Fin 3 → Fin n)
    (occurrence : Fin m) (a : Fin 3 → Ambient s d) :
    (template a).flatMap
        (fun token => encodeWord (evalToken (fun j => (names occurrence j).val)
          occurrence.val token)) =
      encodeWords (recordWords (ActualCanonical.record names occurrence a)) := by
  rw [flatMap_encodeWord, eval_template]

end UniqueGamesTheorem.Reduction.CanonicalWordTemplate

end

end OAI
