import Mathlib
import OAI.Computability.MaxCut.Encoding.TableKeysGame
import OAI.Computability.MaxCut.Games.ActualCompleteness

namespace OAI

/-!
Completeness of the v2 single-orbit matrix game. The generic finite-average
calculation is shared with the proved actual completeness calculation. Its
reuse is justified below by pointwise equality of restored answers under
diagonal labels; the output vertices themselves are never doubled.

No gadget existence, dispersion hypothesis, inverse theorem, or legacy
soundness theorem is a premise. The bound includes the exact fair-bit factor
`1 / 2`, and is a statement about the actual finite edge occurrence list.
-/

namespace MaxCutGames.Decoder.TableKeysCompleteness

open MaxCutGames.Integration.BinaryLinear MaxCutGames.Reduction
open ActualSource Foundations.Target
open TableKeysGame
open scoped BigOperators

noncomputable section

/-- Use a single label function on both auxiliary sides, solely to share the
already proved finite-average calculation. This does not change the v2 game. -/
def diagonalLabeling (S : Source) (k s d : Nat)
    (labeling : Fin (vertexCount S k s d) → Fin (2^s)) :
    Fin (ActualGame.vertexCount S k s d) → Fin (2^s) :=
  ActualGame.labelingOf S k s d (fun _ => vertexLabel S k s d labeling)

theorem diagonal_unfolded (S : Source) (k s d : Nat)
    (labeling : Fin (vertexCount S k s d) → Fin (2^s))
    (side : Bool) (q : Query S k s d) :
    ActualGame.unfolded S k s d (diagonalLabeling S k s d labeling) side q =
      unfolded S k s d labeling q := by
  simp only [diagonalLabeling, ActualGame.unfolded,
    ActualGame.sideLabel_labelingOf, unfolded, canonical]

/-- Pointwise-identical matrix tests have exactly the same acceptance average. -/
theorem acceptanceProbability_eq_diagonal (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (labeling : Fin (vertexCount S k s d) → Fin (2^s)) :
    acceptanceProbability S k g labeling =
      ActualGame.acceptanceProbability S k g (diagonalLabeling S k s d labeling) := by
  rw [acceptanceProbability_eq_test, ActualGame.acceptanceProbability_eq_test]
  simp only [diagonal_unfolded, leftQuery, rightQuery]

def honestLabeling (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (A : Fin S.«variables» → Bool) : Fin (vertexCount S k s d) → Fin (2^s) :=
  labelingOf S k s d (ActualCompleteness.honestVertexLabel S k g A)

theorem diagonal_honestLabeling (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (A : Fin S.«variables» → Bool) :
    diagonalLabeling S k s d (honestLabeling S k g A) =
      ActualCompleteness.honestLabeling S k g A := by
  simp only [diagonalLabeling, honestLabeling, vertexLabel_labelingOf,
    ActualCompleteness.honestLabeling]

/-- The removed affine intercept is recovered by gadget equivariance. -/
theorem honest_unfolded (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (A : Fin S.«variables» → Bool) (q : Query S k s d) :
    unfolded S k s d (honestLabeling S k g A) q =
      g.f (ActualCompleteness.evaluate (ActualGame.names S) (fun n => ofBit (A n))
        (canonical S k s d q)) := by
  rw [← diagonal_unfolded S k s d _ false q, diagonal_honestLabeling]
  exact ActualCompleteness.honest_unfolded S k g A false q

/-- On a satisfied tuple, every sampled table evaluates the same homogeneous
answer with first coordinate one. -/
theorem honest_unfolded_valid (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (A : Fin S.«variables» → Bool) (q : Query S k s d)
    (hgood : ∀ j, S.satisfied A (q.1 j) = true) :
    unfolded S k s d (honestLabeling S k g A) q =
      g.f (q.2 (ActualCompleteness.sourcePoint S k A q.1)) := by
  rw [← diagonal_unfolded S k s d _ false q, diagonal_honestLabeling]
  exact ActualCompleteness.honest_unfolded_valid S k g A false q hgood

theorem honest_acceptance_bound (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (A : Fin S.«variables» → Bool) :
    1 - (k : ℚ) * S.failure A - g.stabilityError / 2 ≤
      acceptanceProbability S k g (honestLabeling S k g A) := by
  rw [acceptanceProbability_eq_diagonal, diagonal_honestLabeling]
  exact ActualCompleteness.honest_acceptance_bound S k g A

theorem honest_acceptance_of_bounds (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (A : Fin S.«variables» → Bool) (ξ p ε : ℚ)
    (hsource : S.failure A ≤ ξ) (hstable : g.stabilityError ≤ p)
    (hbudget : (k : ℚ) * ξ + p / 2 ≤ ε) :
    1 - ε ≤ acceptanceProbability S k g (honestLabeling S k g A) := by
  have hm := mul_le_mul_of_nonneg_left hsource (show (0 : ℚ) ≤ k by positivity)
  have hactual := honest_acceptance_bound S k g A
  linarith

/-- Completeness is measured on the generated single-orbit edge occurrences. -/
theorem honest_satisfied_fraction_bound (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (A : Fin S.«variables» → Bool) :
    1 - (k : ℚ) * S.failure A - g.stabilityError / 2 ≤
      (countSatisfied (honestLabeling S k g A)
        (outputInstance S k g).constraints : ℚ) /
        (outputInstance S k g).constraints.length := by
  rw [← acceptanceProbability_eq_count]
  exact honest_acceptance_bound S k g A

theorem completeAt (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (A : Fin S.«variables» → Bool) (error : RationalError)
    (hbudget : (k : ℚ) * S.failure A + g.stabilityError / 2 ≤
      Integration.GapSemantics.errorValue error) :
    CompleteAt error (outputInstance S k g) := by
  apply (Integration.GapSemantics.completeAt_iff error _).2
  refine ⟨honestLabeling S k g A, ?_⟩
  change 1 - Integration.GapSemantics.errorValue error ≤
    (countSatisfied (honestLabeling S k g A)
      (outputInstance S k g).constraints : ℚ) /
      (outputInstance S k g).constraints.length
  have h := honest_satisfied_fraction_bound S k g A
  linarith

theorem completeAt_withEnumeration (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (en : NoiseEnumeration g)
    (A : Fin S.«variables» → Bool) (error : RationalError)
    (hbudget : (k : ℚ) * S.failure A + g.stabilityError / 2 ≤
      Integration.GapSemantics.errorValue error) :
    CompleteAt error (outputInstanceWithEnumeration S k g en) := by
  apply (completeAt_outputInstanceWithEnumeration_iff error S k g en).2
  exact completeAt S k g A error hbudget

end

end MaxCutGames.Decoder.TableKeysCompleteness

/-! Internal serialization of canonical orbit bodies. Each record occupies nine
natural-number words, so record boundaries are independent of the tag. The
outer complement coordinate occupies one leading word. These are injectivity,
deduplication, and output-size statements, not machine running-time claims. -/

namespace MaxCutGames.Reduction.CanonicalEncoding

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

end MaxCutGames.Reduction.CanonicalEncoding

end OAI
