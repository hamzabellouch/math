import Mathlib
import OAI.Analysis.MatrixSigning.Realization.DependentRealization
import OAI.Analysis.MatrixSigning.Complexity.PolynomialOptimize
import OAI.Analysis.MatrixSigning.Complexity.PolynomialMapFamilies

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

variable {ι α β : Type*} {L : ι → ℕ} {ea : α → Word} {eb : β → Word}
lemma runsPoly_tabulateFin {n : α → ℕ} {f : (Σ a,Fin (n a)) → β}
    (r : Realizes (finFamilyCode ea n) eb f) (rn : Realizes ea natCode n) [PolyTime rn]
    (a : ι → α) (ha : IsPoly L (fun i => (ea (a i)).length))
    (hc : ∃p : NaturalPolynomial,∀i j,r.cost ⟨a i,j⟩≤p.eval (L i)) :
    RunsPoly L (r.tabulateFin rn) a := by
  unfold Realizes.tabulateFin
  apply RunsPoly.congr
  apply RunsPoly.then_with (RunsPoly.of_poly _ a ha)
  intro hw
  apply runsPoly_map _ _ hw
  obtain ⟨p,hp⟩ := hc
  refine ⟨p,?_⟩
  intro i x hx
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hx
  exact hp i j
lemma runsPoly_tabulateFin_family {n : α → ℕ} {f : (Σ a,Fin (n a)) → β}
    (r : Realizes (finFamilyCode ea n) eb f) (rn : Realizes ea natCode n) [PolyTime rn]
    (a : ι → α) (ha : IsPoly L (fun i => (ea (a i)).length))
    (hc : RunsPoly (fun s : Σ i,Fin (n (a i)) => L s.1) r (fun s => ⟨a s.1,s.2⟩)) :
    RunsPoly L (r.tabulateFin rn) a := by
  apply runsPoly_tabulateFin r rn a ha
  obtain ⟨p,hp⟩ := hc.cost
  exact ⟨p,fun i j => hp ⟨i,j⟩⟩
lemma isPoly_finFamily {n : α → ℕ} (rn : Realizes ea natCode n) [PolyTime rn]
    (a : ι → α) (ha : IsPoly L (fun i => (ea (a i)).length)) :
    IsPoly (fun s : Σ i,Fin (n (a i)) => L s.1)
      (fun s => (finFamilyCode ea n ⟨a s.1,s.2⟩).length) := by
  have hn := (RunsPoly.of_poly rn a ha).output
  have h := ((isPoly_const L 2).mul ha).add ((isPoly_const L 1).add hn)
  apply (h.reindex (fun s : Σ i,Fin (n (a i)) => s.1)).mono
  intro s
  simp only [finFamilyCode,prodCode_length,natCode,List.length_replicate,Function.comp_apply]
  have hj := s.2.isLt
  omega
end CurrentKS.Realization

end

end OAI
