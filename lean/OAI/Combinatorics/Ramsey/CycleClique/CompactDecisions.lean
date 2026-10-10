import Mathlib
import OAI.Combinatorics.Ramsey.CycleClique.BallPacking
import OAI.Combinatorics.Ramsey.CycleClique.CertificateDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateModel
import OAI.Combinatorics.Ramsey.CycleClique.CompactLabels
import OAI.Combinatorics.Ramsey.CycleClique.FiniteGraphs
import OAI.Combinatorics.Ramsey.CycleClique.LabelDecisions
import OAI.Combinatorics.Ramsey.CycleClique.MatrixBits

namespace OAI

namespace CycleClique
open scoped SimpleGraph

def compactNodupLabels : List ℕ → Bool
  | [] => true
  | a :: L => !(L.contains a) && compactNodupLabels L

theorem compactNodupLabels_spec (L : List ℕ) : compactNodupLabels L = true ↔ L.Nodup := by
  induction L with
  | nil => simp [compactNodupLabels]
  | cons a L ih => simp [compactNodupLabels, ih]

def compactChainLabels (R : ℕ → ℕ → Bool) : List ℕ → Bool
  | [] => true
  | [_] => true
  | a :: b :: L => R a b && compactChainLabels R (b :: L)

theorem compactChainLabels_spec (R : ℕ → ℕ → Bool) (L : List ℕ) :
    compactChainLabels R L = true ↔ L.IsChain (fun a b => R a b = true) := by
  induction L with
  | nil => simp [compactChainLabels]
  | cons a L ih =>
    cases L with
    | nil => simp [compactChainLabels]
    | cons b L => simp [compactChainLabels, List.isChain_cons_cons, ih]

def compactLabelValidBool (n : ℕ) (q : Finset ℕ) (E : List (ℕ × ℕ))
    (C : List (List ℕ)) : Bool :=
  compactNodupLabels C.flatten && C.flatten.all (fun i => decide (i < n)) &&
  C.all (fun c => !c.isEmpty &&
    compactChainLabels (fun a b =>
      (globalEdgeBits E).testBit (Nat.pair a b) ||
      (globalEdgeBits E).testBit (Nat.pair b a)) c &&
    compactChainLabels (fun a b => decide (a ∉ q) || decide (b ∉ q)) c &&
    c.head?.all (fun a => decide (a ∈ q)) &&
    c.getLast?.all (fun a => decide (a ∈ q))) &&
  decide (∀ i ∈ q, i ∈ C.flatten)

theorem compactLabelValidBool_spec (n : ℕ) (q : Finset ℕ) (E : List (ℕ × ℕ))
    (C : List (List ℕ)) : compactLabelValidBool n q E C = true ↔ LabelValid n q E C := by
  unfold LabelValid
  simp only [compactLabelValidBool, Bool.and_eq_true, compactNodupLabels_spec, List.all_eq_true,
    decide_eq_true_eq, compactChainLabels_spec, Bool.or_eq_true, globalEdgeBits_spec,
    Option.all_eq_true, Bool.not_eq_true',
    List.isEmpty_eq_false_iff, Option.mem_def]
  simp only [and_assoc]
  rfl

instance (priority := high) compactBooleanLabelValid (n : ℕ) (q : Finset ℕ)
    (E : List (ℕ × ℕ)) (C : List (List ℕ)) : Decidable (LabelValid n q E C) :=
  decidable_of_iff _ (compactLabelValidBool_spec n q E C)

instance (priority := high) compactBooleanCertificateValid (k t n : ℕ) (q : Finset ℕ)
    (E : List (ℕ × ℕ)) (L e : ℕ) (M : ForbiddenMatrix) (C : FiniteCertificate) :
    Decidable (C.Valid k t n q E L e M) :=
  match C with
  | .system _ | .cycle _ | .packing _ | .edge _ _ => by unfold FiniteCertificate.Valid; infer_instance
  | .forbid i j d R N => by
    unfold FiniteCertificate.Valid
    exact @instDecidableAnd _ _ inferInstance (@instDecidableAnd _ _ inferInstance
      (@instDecidableAnd _ _ (compactBooleanCertificateValid k t (n+d) q (augmentedEdges n E i j d) L e M R)
        (compactBooleanCertificateValid k t n q E L e ((i,j,d)::M) N)))

end CycleClique

end OAI
