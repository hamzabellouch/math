import Mathlib
import OAI.Combinatorics.Ramsey.CycleClique.BallPacking
import OAI.Combinatorics.Ramsey.CycleClique.CertificateModel
import OAI.Combinatorics.Ramsey.CycleClique.FiniteGraphs

namespace OAI

namespace CycleClique
open scoped SimpleGraph

def matrixBits : ForbiddenMatrix → ℕ → ℕ → ℕ
  | [], _, _ => 0
  | (a,b,d) :: M, i, j =>
      if (a = i ∧ b = j) ∨ (a = j ∧ b = i) then 2^d ||| matrixBits M i j
      else matrixBits M i j

theorem matrixBits_spec (M : ForbiddenMatrix) (i j d : ℕ) :
    (matrixBits M i j).testBit d = true ↔ matrixEntry M i j d := by
  induction M with
  | nil => simp [matrixBits, matrixEntry]
  | cons c M ih =>
    rcases c with ⟨a,b,e⟩
    simp only [matrixBits, matrixEntry, List.mem_cons, Prod.mk.injEq] at *
    split_ifs with he
    · rw [Nat.testBit_lor, Nat.testBit_two_pow]
      simp only [Bool.or_eq_true, decide_eq_true_eq, ih]
      rcases he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> tauto
    · rw [ih]
      tauto

instance (priority := high) fastMatrixEntry (M : ForbiddenMatrix) (i j d : ℕ) :
    Decidable (matrixEntry M i j d) := decidable_of_iff _ (matrixBits_spec M i j d)

instance (priority := high) fastExcluded (n : ℕ) (M : ForbiddenMatrix)
    (i lo hi : ℕ) (Z : Finset ℕ) : Decidable (Excluded n M i lo hi Z) := by
  unfold Excluded
  infer_instance

instance (priority := high) fastBallValid (k t n : ℕ) (M : ForbiddenMatrix) (i : ℕ)
    (B : BallCertificate) : Decidable (B.Valid k t n M i) :=
  match B with
  | .zero Z b u => by unfold BallCertificate.Valid; infer_instance
  | .succ p Z b u => by
    unfold BallCertificate.Valid
    exact @instDecidableAnd _ _ (fastBallValid k t n M i p) inferInstance

instance (priority := high) fastPackingOptionValid (k t n : ℕ)
    (M : ForbiddenMatrix) (o : PackingOption) : Decidable (o.Valid k t n M) := by
  cases o <;> unfold PackingOption.Valid <;> infer_instance

instance (priority := high) fastPackingCompatible (M : ForbiddenMatrix)
    (a b : PackingOption) : Decidable (a.Compatible M b) := by
  unfold PackingOption.Compatible
  infer_instance

instance (priority := high) fastPackingValid (k t n : ℕ)
    (M : ForbiddenMatrix) (P : Finset PackingOption) : Decidable (PackingValid k t n M P) := by
  unfold PackingValid
  infer_instance

instance (priority := high) fastCertificateValid (k t n : ℕ) (q : Finset ℕ)
    (E : List (ℕ × ℕ)) (L e : ℕ) (M : ForbiddenMatrix) (C : FiniteCertificate) :
    Decidable (C.Valid k t n q E L e M) :=
  match C with
  | .system _ | .cycle _ | .packing _ | .edge _ _ => by unfold FiniteCertificate.Valid; infer_instance
  | .forbid i j d R N => by
    unfold FiniteCertificate.Valid
    exact @instDecidableAnd _ _ inferInstance (@instDecidableAnd _ _ inferInstance
      (@instDecidableAnd _ _ (fastCertificateValid k t (n+d) q (augmentedEdges n E i j d) L e M R)
        (fastCertificateValid k t n q E L e ((i,j,d)::M) N)))

end CycleClique

end OAI
