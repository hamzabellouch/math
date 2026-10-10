import Mathlib
import OAI.Analysis.MatrixSigning.Complexity.PolynomialLoops
import OAI.Analysis.MatrixSigning.Complexity.PolynomialFamilies

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

local notation "X" => NaturalPolynomial.variable
variable {ι α β : Type*} {L : ι → ℕ} {ea : α → Word} {eb : β → Word} {f : α → β}
lemma runsPoly_map (r : Realizes ea eb f) (xs : ι → List α)
    (ha : IsPoly L (fun i => (listCode ea (xs i)).length))
    (hc : ∃ p : NaturalPolynomial,∀i x,x∈xs i → r.cost x≤p.eval (L i)) :
    RunsPoly L r.map xs := by
  obtain ⟨p,hp⟩ := hc
  obtain ⟨q,hq⟩ := ha
  refine ⟨⟨q,hq⟩,⟨2*q+q*(3*q+p+6*(q+p)+8)+q*(2*(q+p)+1)+4,?_⟩⟩
  intro i
  let A := q.eval (L i)
  let C := p.eval (L i)
  have hn : (xs i).length≤A := (list_length_le_code ea (xs i)).trans (hq i)
  have he : ∀x∈xs i,(ea x).length≤A := fun x hx => (mem_length_le_code (xs i) hx).trans (hq i)
  have ho : ∀x∈xs i,(eb (f x)).length≤A+C := fun x hx =>
    (r.output_length x).trans (Nat.add_le_add (he x hx) (hp i x hx))
  have hs := sum_map_bound (xs i) (fun x => FramedMapRoutine.bodyTicks ea (fun x => eb (f x)) r.cost x+1)
    (3*A+C+6*(A+C)+8) (by
      intro x hx
      have hl := he x hx
      have hc' := hp i x hx
      have hout := ho x hx
      simp only [FramedMapRoutine.bodyTicks,KS.W01.length_frame]
      omega)
  have ht := listCode_length_bound (ea:=fun x => eb (f x)) (xs i) (A+C) ho
  have hs' := hs.trans (Nat.mul_le_mul_right _ hn)
  have ht' := ht.trans (Nat.mul_le_mul_right _ hn)
  change FramedMapRoutine.ticks ea (fun x => eb (f x)) r.cost (xs i)≤_
  simp only [FramedMapRoutine.ticks,FramedMapRoutine.scanTicks]
  change 2*(listCode ea (xs i)).length+2+((xs i).map _).sum+1+
    (listCode (fun x => eb (f x)) (xs i)).length+1≤_
  change _≤2*A+A*(3*A+C+6*(A+C)+8)+A*(2*(A+C)+1)+4
  have hl : (listCode ea (xs i)).length≤A := hq i
  omega
end CurrentKS.Realization

end

end OAI
