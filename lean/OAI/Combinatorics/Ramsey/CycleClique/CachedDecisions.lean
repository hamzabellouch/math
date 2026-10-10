import Mathlib
import OAI.Combinatorics.Ramsey.CycleClique.BallPacking
import OAI.Combinatorics.Ramsey.CycleClique.CertificateDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateModel
import OAI.Combinatorics.Ramsey.CycleClique.CliqueBits
import OAI.Combinatorics.Ramsey.CycleClique.CompactDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CompactLabels
import OAI.Combinatorics.Ramsey.CycleClique.EdgeBits
import OAI.Combinatorics.Ramsey.CycleClique.EdgeDecisions
import OAI.Combinatorics.Ramsey.CycleClique.FiniteGraphs
import OAI.Combinatorics.Ramsey.CycleClique.LabelDecisions
import OAI.Combinatorics.Ramsey.CycleClique.MatrixBits

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem qCacheEdgeBits_append (E F : List (ℕ × ℕ)) :
    globalEdgeBits (E ++ F) = globalEdgeBits E ||| globalEdgeBits F := by
  induction E with
  | nil => simp [globalEdgeBits]
  | cons ab E ih =>
    rcases ab with ⟨a,b⟩
    simp only [List.cons_append, globalEdgeBits, ih, Nat.lor_assoc]

def qCachedLabelValidBool (n : ℕ) (q : Finset ℕ) (bits : ℕ)
    (C : List (List ℕ)) : Bool :=
  compactNodupLabels C.flatten && C.flatten.all (fun i => decide (i < n)) &&
  C.all (fun c => !c.isEmpty &&
    compactChainLabels (fun a b => bits.testBit (Nat.pair a b) ||
      bits.testBit (Nat.pair b a)) c &&
    compactChainLabels (fun a b => (!(qBits q).testBit a) || (!(qBits q).testBit b)) c &&
    c.head?.all (fun a => (qBits q).testBit a) &&
    c.getLast?.all (fun a => (qBits q).testBit a)) &&
  decide (∀ i ∈ q, i ∈ C.flatten)

theorem qCachedLabelValidBool_spec (n : ℕ) (q : Finset ℕ) (E : List (ℕ × ℕ))
    (C : List (List ℕ)) :
    qCachedLabelValidBool n q (globalEdgeBits E) C = true ↔ LabelValid n q E C :=
  by
    have hf (i : ℕ) : (qBits q).testBit i = false ↔ i ∉ q := by
      rw [Bool.eq_false_iff]
      exact not_congr (qBits_spec q i)
    unfold LabelValid
    simp only [qCachedLabelValidBool, Bool.and_eq_true, compactNodupLabels_spec,
      List.all_eq_true, decide_eq_true_eq, compactChainLabels_spec,
      Bool.or_eq_true, globalEdgeBits_spec, qBits_spec, Option.all_eq_true,
      Bool.not_eq_true', hf, List.isEmpty_eq_false_iff, Option.mem_def]
    simp only [and_assoc]
    rfl

def qCachedCycleValidBool (n k bits : ℕ) (C : List ℕ) : Bool :=
  compactNodupLabels C && decide (C.length = k+1) &&
  C.all (fun i => decide (i<n)) &&
  compactChainLabels (fun a b => bits.testBit (Nat.pair a b) ||
    bits.testBit (Nat.pair b a)) C &&
  C.head?.all (fun a => C.getLast?.all (fun b =>
    bits.testBit (Nat.pair a b) || bits.testBit (Nat.pair b a)))

theorem qCachedCycleValidBool_spec (n k : ℕ) (E : List (ℕ × ℕ)) (C : List ℕ) :
    qCachedCycleValidBool n k (globalEdgeBits E) C = true ↔ LabelCycleValid n k E C := by
  simp only [qCachedCycleValidBool, LabelCycleValid, Bool.and_eq_true,
    compactNodupLabels_spec, decide_eq_true_eq, List.all_eq_true,
    compactChainLabels_spec, Bool.or_eq_true, globalEdgeBits_spec,
    Option.all_eq_true, labelAdj, Option.mem_def, and_assoc]
  simp only [or_comm]
  rfl

def qCachedCertificateBool (k t n : ℕ) (q : Finset ℕ) (bits : ℕ) (L e : ℕ)
    (M : ForbiddenMatrix) : FiniteCertificate → Bool
  | .system C => qCachedLabelValidBool n q bits C && decide (Improvement k t L e C)
  | .cycle C => qCachedCycleValidBool n k bits C
  | .packing P => decide (PackingValid k t n M P)
  | .edge i j => decide (i < n) && decide (j < n) &&
      (bits.testBit (Nat.pair i j) || bits.testBit (Nat.pair j i)) &&
      decide (matrixEntry M i j 0)
  | .forbid i j d R N => decide (i < n) && decide (j < n) &&
      qCachedCertificateBool k t (n+d) q
        (bits ||| globalEdgeBits (pathEdges (pathLabels n i j d))) L e M R &&
      qCachedCertificateBool k t n q bits L e ((i,j,d)::M) N

theorem qCachedCertificateBool_spec (k t n : ℕ) (q : Finset ℕ) (E : List (ℕ × ℕ))
    (L e : ℕ) (M : ForbiddenMatrix) (C : FiniteCertificate) :
    qCachedCertificateBool k t n q (globalEdgeBits E) L e M C = true ↔
      C.Valid k t n q E L e M := by
  induction C generalizing n E M with
  | system C => simp [qCachedCertificateBool, FiniteCertificate.Valid, qCachedLabelValidBool_spec]
  | cycle C => exact qCachedCycleValidBool_spec n k E C
  | packing P => simp [qCachedCertificateBool, FiniteCertificate.Valid]
  | edge i j =>
    simp [qCachedCertificateBool, FiniteCertificate.Valid, globalEdgeBits_spec, labelAdj, and_assoc]
  | forbid i j d R N ihR ihN =>
    simp only [qCachedCertificateBool, Bool.and_eq_true, decide_eq_true_eq]
    rw [← qCacheEdgeBits_append, ← augmentedEdges, ihR, ihN]
    simp only [FiniteCertificate.Valid, and_assoc]

instance (priority := high) qCachedCertificateValid (k t n : ℕ) (q : Finset ℕ)
    (E : List (ℕ × ℕ)) (L e : ℕ) (M : ForbiddenMatrix) (C : FiniteCertificate) :
    Decidable (C.Valid k t n q E L e M) :=
  decidable_of_iff _ (qCachedCertificateBool_spec k t n q E L e M C)

end CycleClique

end OAI
