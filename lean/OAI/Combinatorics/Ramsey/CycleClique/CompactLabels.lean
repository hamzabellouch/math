import Mathlib
import OAI.Combinatorics.Ramsey.CycleClique.BallPacking
import OAI.Combinatorics.Ramsey.CycleClique.CertificateDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateModel
import OAI.Combinatorics.Ramsey.CycleClique.FiniteGraphs
import OAI.Combinatorics.Ramsey.CycleClique.LabelDecisions
import OAI.Combinatorics.Ramsey.CycleClique.MatrixBits

namespace OAI

namespace CycleClique
open scoped SimpleGraph

instance (priority := high) compactLabelCycleValid (n k : ℕ)
    (E : List (ℕ × ℕ)) (C : List ℕ) : Decidable (LabelCycleValid n k E C) := by
  unfold LabelCycleValid
  infer_instance

instance (priority := high) compactAllCertificateValid (k t n : ℕ) (q : Finset ℕ)
    (E : List (ℕ × ℕ)) (L e : ℕ) (M : ForbiddenMatrix) (C : FiniteCertificate) :
    Decidable (C.Valid k t n q E L e M) :=
  match C with
  | .system _ | .cycle _ | .packing _ | .edge _ _ => by unfold FiniteCertificate.Valid; infer_instance
  | .forbid i j d R N => by
    unfold FiniteCertificate.Valid
    exact @instDecidableAnd _ _ inferInstance (@instDecidableAnd _ _ inferInstance
      (@instDecidableAnd _ _ (compactAllCertificateValid k t (n+d) q (augmentedEdges n E i j d) L e M R)
        (compactAllCertificateValid k t n q E L e ((i,j,d)::M) N)))

end CycleClique

end OAI
