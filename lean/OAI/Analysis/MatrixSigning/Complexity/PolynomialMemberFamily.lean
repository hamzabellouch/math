import Mathlib
import OAI.Analysis.MatrixSigning.Complexity.PolynomialLoops
import OAI.Analysis.MatrixSigning.Complexity.PolynomialFamilies

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

variable {ι α : Type*} {L : ι → ℕ} {ea : α → Word}
lemma isPoly_listMember (xs : ι → List α)
    (ha : IsPoly L (fun i => (listCode ea (xs i)).length)) :
    IsPoly (fun s : Σ i,{x // x∈xs i} => L s.1)
      (fun s => (ea s.2.val).length) :=
  (ha.reindex Sigma.fst).mono (fun s => mem_length_le_code (xs s.1) s.2.property)
end CurrentKS.Realization

end

end OAI
