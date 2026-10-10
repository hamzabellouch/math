import Mathlib
import OAI.Combinatorics.Ramsey.CycleClique.BallPacking
import OAI.Combinatorics.Ramsey.CycleClique.CertificateModel
import OAI.Combinatorics.Ramsey.CycleClique.FiniteGraphs
import OAI.Combinatorics.Ramsey.CycleClique.MatrixBits

namespace OAI

namespace CycleClique
open scoped SimpleGraph

def globalEdgeBits : List (ℕ × ℕ) → ℕ
  | [] => 0
  | (a,b) :: E => 2^(Nat.pair a b) ||| globalEdgeBits E

theorem globalEdgeBits_spec (E : List (ℕ × ℕ)) (a b : ℕ) :
    (globalEdgeBits E).testBit (Nat.pair a b) = true ↔ (a,b) ∈ E := by
  induction E with
  | nil => simp [globalEdgeBits]
  | cons e E ih =>
    rcases e with ⟨i,j⟩
    simp only [globalEdgeBits, Nat.testBit_lor, Nat.testBit_two_pow, Bool.or_eq_true,
      decide_eq_true_eq, Nat.pair_eq_pair, ih, List.mem_cons, Prod.mk.injEq]
    tauto

instance (priority := high) globalLabelAdj (E : List (ℕ × ℕ)) (a b : ℕ) :
    Decidable (labelAdj E a b) :=
  decidable_of_iff ((globalEdgeBits E).testBit (Nat.pair a b) = true ∨
    (globalEdgeBits E).testBit (Nat.pair b a) = true)
    (by simp only [globalEdgeBits_spec, labelAdj])

instance (priority := high) globalLabelValid (n : ℕ) (q : Finset ℕ)
    (E : List (ℕ × ℕ)) (C : List (List ℕ)) : Decidable (LabelValid n q E C) := by
  unfold LabelValid
  infer_instance

instance (priority := high) globalCertificateValid (k t n : ℕ) (q : Finset ℕ)
    (E : List (ℕ × ℕ)) (L e : ℕ) (M : ForbiddenMatrix) (C : FiniteCertificate) :
    Decidable (C.Valid k t n q E L e M) :=
  match C with
  | .system _ | .cycle _ | .packing _ | .edge _ _ => by unfold FiniteCertificate.Valid; infer_instance
  | .forbid i j d R N => by
    unfold FiniteCertificate.Valid
    exact @instDecidableAnd _ _ inferInstance (@instDecidableAnd _ _ inferInstance
      (@instDecidableAnd _ _ (globalCertificateValid k t (n+d) q (augmentedEdges n E i j d) L e M R)
        (globalCertificateValid k t n q E L e ((i,j,d)::M) N)))

end CycleClique

end OAI
