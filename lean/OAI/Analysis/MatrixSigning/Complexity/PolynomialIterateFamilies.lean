import Mathlib
import OAI.Analysis.MatrixSigning.Complexity.PolynomialLoops
import OAI.Analysis.MatrixSigning.Complexity.PolynomialFamilies

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

variable {ι α : Type*} {L : ι → ℕ} {ea : α → Word} {f : α → α}
lemma runsPoly_iterate (r : Realizes ea ea f) (a : ι → ℕ×α)
    (ha : IsPoly L (fun i => (prodCode natCode ea (a i)).length))
    (hc : ∃p : NaturalPolynomial,∀i j,j<(a i).1 → r.cost (f^[j] (a i).2)≤p.eval (L i)) :
    RunsPoly L r.iterate a := by
  obtain ⟨p,hp⟩ := ha
  obtain ⟨q,hq⟩ := hc
  refine ⟨⟨p,hp⟩,⟨3*p+p*(q+2)+3,?_⟩⟩
  intro i
  have hn : (a i).1≤p.eval (L i) := by
    have h := hp i
    simp only [prodCode_length,natCode,List.length_replicate] at h
    omega
  have ht := iterate_ticks_bound r (a i).2 (a i).1 (q.eval (L i)) (hq i)
  have ht' := ht.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hn) 1)
  change 3*(a i).1+2+IterateRoutine.loopTicks r.cost f (a i).1 (a i).2≤
    3*p.eval (L i)+p.eval (L i)*(q.eval (L i)+2)+3
  omega
end CurrentKS.Realization

end

end OAI
