import Mathlib
import OAI.Combinatorics.Ramsey.CycleClique.BallPacking
import OAI.Combinatorics.Ramsey.CycleClique.CertificateModel
import OAI.Combinatorics.Ramsey.CycleClique.FiniteGraphs
import OAI.Combinatorics.Ramsey.CycleClique.LabelDecisions
import OAI.Combinatorics.Ramsey.CycleClique.MatrixBits

namespace OAI

namespace CycleClique
open scoped SimpleGraph

def compactTriple (a b d : ℕ) : ℕ :=
  Nat.pair (Nat.pair (a / 32) (b / 32)) (d / 8) * 8192 +
    (a % 32) * 256 + (b % 32) * 8 + d % 8

theorem compactTriple_injective {a b d i j e : ℕ} :
    compactTriple a b d = compactTriple i j e ↔ a = i ∧ b = j ∧ d = e := by
  constructor
  · intro h
    unfold compactTriple at h
    have hbig : Nat.pair (Nat.pair (a / 32) (b / 32)) (d / 8) =
        Nat.pair (Nat.pair (i / 32) (j / 32)) (e / 8) := by omega
    obtain ⟨hp, hd⟩ := Nat.pair_eq_pair.mp hbig
    obtain ⟨ha, hb⟩ := Nat.pair_eq_pair.mp hp
    omega
  · rintro ⟨rfl,rfl,rfl⟩
    rfl

def compactMatrixBits : ForbiddenMatrix → ℕ
  | [] => 0
  | (a,b,d) :: M => 2^(compactTriple a b d) ||| compactMatrixBits M

theorem compactMatrixBits_spec (M : ForbiddenMatrix) (i j d : ℕ) :
    (compactMatrixBits M).testBit (compactTriple i j d) = true ↔ (i,j,d) ∈ M := by
  induction M with
  | nil => simp [compactMatrixBits]
  | cons c M ih =>
    rcases c with ⟨a,b,e⟩
    simp only [compactMatrixBits, Nat.testBit_lor, Nat.testBit_two_pow,
      Bool.or_eq_true, decide_eq_true_eq, compactTriple_injective, ih,
      List.mem_cons, Prod.mk.injEq]
    tauto

instance (priority := high) compactMatrixEntry (M : ForbiddenMatrix) (i j d : ℕ) :
    Decidable (matrixEntry M i j d) :=
  decidable_of_iff ((compactMatrixBits M).testBit (compactTriple i j d) = true ∨
    (compactMatrixBits M).testBit (compactTriple j i d) = true)
    (by simp only [compactMatrixBits_spec, matrixEntry])

instance (priority := high) compactExcluded (n : ℕ) (M : ForbiddenMatrix)
    (i lo hi : ℕ) (Z : Finset ℕ) : Decidable (Excluded n M i lo hi Z) := by
  unfold Excluded
  infer_instance

instance (priority := high) compactBallValid (k t n : ℕ) (M : ForbiddenMatrix) (i : ℕ)
    (B : BallCertificate) : Decidable (B.Valid k t n M i) :=
  match B with
  | .zero Z b u => by unfold BallCertificate.Valid; infer_instance
  | .succ p Z b u => by
    unfold BallCertificate.Valid
    exact @instDecidableAnd _ _ (compactBallValid k t n M i p) inferInstance

instance (priority := high) compactPackingOptionValid (k t n : ℕ)
    (M : ForbiddenMatrix) (o : PackingOption) : Decidable (o.Valid k t n M) := by
  cases o <;> unfold PackingOption.Valid <;> infer_instance

instance (priority := high) compactPackingCompatible (M : ForbiddenMatrix)
    (a b : PackingOption) : Decidable (a.Compatible M b) := by
  unfold PackingOption.Compatible
  infer_instance

instance (priority := high) compactPackingValid (k t n : ℕ)
    (M : ForbiddenMatrix) (P : Finset PackingOption) : Decidable (PackingValid k t n M P) := by
  unfold PackingValid
  infer_instance

instance (priority := high) compactMatrixCertificateValid (k t n : ℕ) (q : Finset ℕ)
    (E : List (ℕ × ℕ)) (L e : ℕ) (M : ForbiddenMatrix) (C : FiniteCertificate) :
    Decidable (C.Valid k t n q E L e M) :=
  match C with
  | .system _ | .cycle _ | .packing _ | .edge _ _ => by unfold FiniteCertificate.Valid; infer_instance
  | .forbid i j d R N => by
    unfold FiniteCertificate.Valid
    exact @instDecidableAnd _ _ inferInstance (@instDecidableAnd _ _ inferInstance
      (@instDecidableAnd _ _ (compactMatrixCertificateValid k t (n+d) q (augmentedEdges n E i j d) L e M R)
        (compactMatrixCertificateValid k t n q E L e ((i,j,d)::M) N)))

end CycleClique

end OAI
