import Mathlib
import OAI.Combinatorics.Ramsey.CycleClique.BallPacking
import OAI.Combinatorics.Ramsey.CycleClique.CertificateDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateModel
import OAI.Combinatorics.Ramsey.CycleClique.CompactDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CompactLabels
import OAI.Combinatorics.Ramsey.CycleClique.FiniteGraphs
import OAI.Combinatorics.Ramsey.CycleClique.LabelDecisions
import OAI.Combinatorics.Ramsey.CycleClique.MatrixBits

namespace OAI

namespace CycleClique
open scoped SimpleGraph

def compactCertificateBool (k t n : ℕ) (q : Finset ℕ) (E : List (ℕ × ℕ)) (L e : ℕ)
    (M : ForbiddenMatrix) : FiniteCertificate → Bool
  | .system C => compactLabelValidBool n q E C && decide (Improvement k t L e C)
  | .cycle C => decide (LabelCycleValid n k E C)
  | .packing P => decide (PackingValid k t n M P)
  | .edge i j => decide (i < n) && decide (j < n) &&
      decide (labelAdj E i j) && decide (matrixEntry M i j 0)
  | .forbid i j d R N => decide (i < n) && decide (j < n) &&
      compactCertificateBool k t (n+d) q (augmentedEdges n E i j d) L e M R &&
      compactCertificateBool k t n q E L e ((i,j,d)::M) N

theorem compactCertificateBool_spec (k t n : ℕ) (q : Finset ℕ) (E : List (ℕ × ℕ))
    (L e : ℕ) (M : ForbiddenMatrix) (C : FiniteCertificate) :
    compactCertificateBool k t n q E L e M C = true ↔ C.Valid k t n q E L e M := by
  induction C generalizing n E M with
  | system C => simp [compactCertificateBool, FiniteCertificate.Valid, compactLabelValidBool_spec]
  | cycle C => simp [compactCertificateBool, FiniteCertificate.Valid]
  | packing P => simp [compactCertificateBool, FiniteCertificate.Valid]
  | edge i j => simp [compactCertificateBool, FiniteCertificate.Valid, and_assoc]
  | forbid i j d R N ihR ihN =>
    simp [compactCertificateBool, FiniteCertificate.Valid, ihR, ihN, and_assoc]

instance (priority := high) fullyCompactCertificateValid (k t n : ℕ) (q : Finset ℕ)
    (E : List (ℕ × ℕ)) (L e : ℕ) (M : ForbiddenMatrix) (C : FiniteCertificate) :
    Decidable (C.Valid k t n q E L e M) :=
  decidable_of_iff _ (compactCertificateBool_spec k t n q E L e M C)

end CycleClique

end OAI
