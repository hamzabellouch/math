import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Data.Set.Finite.Range

namespace OAI

universe uX uLabel uY

/-!
# Fixed encodings of realized partition labels

Only the realized labels are counted. The ambient label types need not be
finite, and representatives are fixed from the label maps alone, before any
coefficient vector enters the compression construction.
-/

noncomputable section

namespace MetricEntropyDuality

/-- Shared finite label data for a family of partitions. A representative is
defined at every code, including unused codes, and preserves each realized
label when applied to its encoding. -/
structure FixedLabels {X : Type uX} {u : ℕ} {Label : Fin u → Type uLabel}
    (L : (i : Fin u) → X → Label i) (q : ℕ) where
  encode : Fin u → X → Fin q
  representative : Fin u → Fin q → X
  encode_eq_iff : ∀ i x y, encode i x = encode i y ↔ L i x = L i y
  label_representative_encode : ∀ i x,
    L i (representative i (encode i x)) = L i x

namespace FixedLabels

variable {X : Type uX} {u q : ℕ} {Label : Fin u → Type uLabel}
  {L : (i : Fin u) → X → Label i}

/-- Embed the finite range, rather than the entire ambient label type. -/
def rangeEmbedding {Y : Type uY} [Finite X] (f : X → Y) (q : ℕ)
    (hcard : Nat.card (Set.range f) ≤ q) : Set.range f ↪ Fin q :=
  (Finite.equivFin (Set.range f)).toEmbedding.trans (Fin.castLEEmb hcard)

/-- Construct all encodings and representative maps from the fixed label
family and its realized-cardinality bounds. The construction has no measure
or coefficient-vector parameter. Nonempty `X` supplies a representative even
at codes outside the encoding's image. -/
def ofCardBound [Finite X] [Nonempty X]
    (L : (i : Fin u) → X → Label i)
    (hcard : ∀ i, Nat.card (Set.range (L i)) ≤ q) : FixedLabels L q := by
  let enc : Fin u → X → Fin q := fun i x =>
    rangeEmbedding (L i) q (hcard i) ⟨L i x, ⟨x, rfl⟩⟩
  have heq : ∀ i x y, enc i x = enc i y ↔ L i x = L i y := by
    intro i x y
    constructor
    · intro h
      exact congrArg Subtype.val ((rangeEmbedding (L i) q (hcard i)).injective h)
    · intro h
      exact congrArg (rangeEmbedding (L i) q (hcard i)) (Subtype.ext h)
  let rep : Fin u → Fin q → X := fun i => Function.invFun (enc i)
  have hrep : ∀ i x, L i (rep i (enc i x)) = L i x := by
    intro i x
    apply (heq i _ _).mp
    exact Function.invFun_eq ⟨x, rfl⟩
  exact ⟨enc, rep, heq, hrep⟩

/-- Replacing a vertex by its fixed representative keeps its finite code. -/
theorem encode_representative_encode (E : FixedLabels L q) (i : Fin u) (x : X) :
    E.encode i (E.representative i (E.encode i x)) = E.encode i x :=
  (E.encode_eq_iff i _ _).mpr (E.label_representative_encode i x)

/-- Equal labels select the same fixed representative. -/
theorem representative_encode_eq_of_label_eq (E : FixedLabels L q)
    (i : Fin u) {x y : X} (h : L i x = L i y) :
    E.representative i (E.encode i x) = E.representative i (E.encode i y) := by
  rw [(E.encode_eq_iff i x y).mpr h]

/-- A fixed vertex supplies a realized code for padding unused pivot slots. -/
def paddingCode [Nonempty X] (E : FixedLabels L q) (i : Fin u) : Fin q :=
  E.encode i (Classical.choice ‹Nonempty X›)

theorem paddingCode_realized [Nonempty X] (E : FixedLabels L q) (i : Fin u) :
    ∃ x : X, E.encode i x = E.paddingCode i :=
  ⟨Classical.choice ‹Nonempty X›, rfl⟩

end FixedLabels

end MetricEntropyDuality

end

end OAI
