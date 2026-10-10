import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSupportConverseTests
import OAI.NumberTheory.Ostmann.Construction.CanonicalOccurrenceTransportPairRows

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkReferenceTests
open Construction Construction.CanonicalOccurrenceTransport Characters.RationalHistory
open HistorySymbolicEncoding HistoryOccurrenceVariables HistoryPairPattern HistoryPairRows ClearedCoefficientFlags
open HistoryBulkSupportConverse HistoryBulkSupportConversePlan MvPolynomial

theorem left_flags_eval_normalized (seed : List SourceSlot) {l : ℕ}
    {V : ℕ → ℕ} {outside : List ℕ} (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hh : TreeSourceLabels seed h) (i : Internal seed l)
    (v : PairKey h k → ℤ) (z : Coordinate seed l → ℤ)
    (hv : ∀ q, v (leftMap h k q) = z ((coordinateEquiv seed h hh).symm q)) :
    eval v (leftFlag h k hs ks (.inl (internalEquiv seed h hh i))) =
      eval z (leftCoefficient (normalizedRows seed h hs hh i).1
        (normalizedRows seed h hs hh i).2) ∧
    eval v (rightFlag h k hs ks (.inl (internalEquiv seed h hh i))) =
      eval z (rightCoefficient (normalizedRows seed h hs hh i).1
        (normalizedRows seed h hs hh i).2) := by
  have he : v ∘ leftMap h k = z ∘ (coordinateEquiv seed h hh).symm := funext hv
  simp only [leftFlag, rightFlag, row, Sum.elim_inl, normalizedRows,
    ← leftCoefficient_rename, ← rightCoefficient_rename, eval_rename, he, and_self]

theorem right_flags_eval_normalized (seed : List SourceSlot) {l : ℕ}
    {V : ℕ → ℕ} {outside : List ℕ} (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hk : TreeSourceLabels seed k) (i : Internal seed l)
    (v : PairKey h k → ℤ) (z : Coordinate seed l → ℤ)
    (hv : ∀ q, v (rightMap h k q) = z ((coordinateEquiv seed k hk).symm q)) :
    eval v (leftFlag h k hs ks (.inr (internalEquiv seed k hk i))) =
      eval z (leftCoefficient (normalizedRows seed k ks hk i).1
        (normalizedRows seed k ks hk i).2) ∧
    eval v (rightFlag h k hs ks (.inr (internalEquiv seed k hk i))) =
      eval z (rightCoefficient (normalizedRows seed k ks hk i).1
        (normalizedRows seed k ks hk i).2) := by
  have he : v ∘ rightMap h k = z ∘ (coordinateEquiv seed k hk).symm := funext hv
  simp only [leftFlag, rightFlag, row, Sum.elim_inr, normalizedRows,
    ← leftCoefficient_rename, ← rightCoefficient_rename, eval_rename, he, and_self]

theorem left_line_eq_reference (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (outside : List ℕ) (l : ℕ) (a b : State)
    (c : HistoryChoices sources seed V l)
    (ha : Template.Matches (Template.current seed l) a.small)
    (hb : Template.Matches (Template.current seed l) b.small)
    (hs : (decodeHistory sources seed V l a c).Supported V outside)
    (k : History l) (ks : k.Supported V outside)
    (v : PairKey (decodeHistory sources seed V l a c) k → ℤ) (Xp Xm : ℤ)
    (hv : ∀ q, v (leftMap _ k q) =
      newIntegerSample sources seed V l b c hb Xp Xm
        ((decodedCoordinateEquiv sources seed V l a c ha).symm q))
    (i : Internal seed l) :
    eval v (leftFlag _ k hs ks (.inl (internalEquiv seed _
      (decoded_tree_source_labels sources seed V l a c ha) i)))*Xp +
    eval v (rightFlag _ k hs ks (.inl (internalEquiv seed _
      (decoded_tree_source_labels sources seed V l a c ha) i)))*Xm =
      referenceLine sources seed V outside l a b c ha hb hs Xp Xm i := by
  obtain ⟨hleft, hright⟩ := left_flags_eval_normalized seed _ k hs ks
    (decoded_tree_source_labels sources seed V l a c ha) i v
    (newIntegerSample sources seed V l b c hb Xp Xm) hv
  rw [hleft, hright]
  rfl

theorem right_line_eq_reference (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (outside : List ℕ) (l : ℕ) (a b : State)
    (c : HistoryChoices sources seed V l)
    (ha : Template.Matches (Template.current seed l) a.small)
    (hb : Template.Matches (Template.current seed l) b.small)
    (ks : (decodeHistory sources seed V l a c).Supported V outside)
    (h : History l) (hs : h.Supported V outside)
    (v : PairKey h (decodeHistory sources seed V l a c) → ℤ) (Xp Xm : ℤ)
    (hv : ∀ q, v (rightMap h _ q) =
      newIntegerSample sources seed V l b c hb Xp Xm
        ((decodedCoordinateEquiv sources seed V l a c ha).symm q))
    (i : Internal seed l) :
    eval v (leftFlag h _ hs ks (.inr (internalEquiv seed _
      (decoded_tree_source_labels sources seed V l a c ha) i)))*Xp +
    eval v (rightFlag h _ hs ks (.inr (internalEquiv seed _
      (decoded_tree_source_labels sources seed V l a c ha) i)))*Xm =
      referenceLine sources seed V outside l a b c ha hb ks Xp Xm i := by
  obtain ⟨hleft, hright⟩ := right_flags_eval_normalized seed h _ hs ks
    (decoded_tree_source_labels sources seed V l a c ha) i v
    (newIntegerSample sources seed V l b c hb Xp Xm) hv
  rw [hleft, hright]
  rfl

end Ostmann.Arithmetic.HistoryBulkReferenceTests

end

end OAI
