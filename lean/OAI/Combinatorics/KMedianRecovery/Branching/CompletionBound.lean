import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.FiniteContinuation
import OAI.Combinatorics.KMedianRecovery.Recovery.LengthPolynomial

namespace OAI

namespace MetricKMedianRecovery.RationalPhase
lemma finish_events {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (fuel : ℕ) (s : State m d) :
    (finish distance F v lam fuel s).2.length≤fuel ∧
      ∀ e∈(finish distance F v lam fuel s).2,e.facility∈F := by
  induction fuel generalizing s with
  | zero=>simp only [finish,List.length_nil,List.not_mem_nil,false_implies,implies_true,and_true,Nat.zero_le]
  | succ n ih=>
    rw [finish]
    split
    next h=>simp only [List.length_nil,List.not_mem_nil,false_implies,implies_true,and_true,Nat.zero_le]
    next e he=>
      obtain ⟨hlen,hmem⟩:=ih (update distance v s e)
      refine ⟨by simpa only [List.length_cons] using Nat.succ_le_succ hlen,?_⟩
      intro t ht
      rcases List.mem_cons.mp ht with rfl|ht
      · exact (first_some distance F s.opened v s.phase lam _ t he).1
      · exact hmem t ht
lemma completion_events {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F Q : Finset (Fin m))
    (v z lam : ℚ) :
    (completion distance F v z lam Q).length≤F.card ∧
      ∀ i∈completion distance F v z lam Q,i∈F := by
  obtain ⟨hlen,hmem⟩:=finish_events distance F v lam F.card ⟨Q,z,Vector.replicate d 0⟩
  refine ⟨by simpa only [completion,List.length_map] using hlen,?_⟩
  intro i hi
  obtain ⟨e,he,rfl⟩:=List.mem_map.mp hi
  exact hmem e he
end MetricKMedianRecovery.RationalPhase

namespace MetricKMedianRecovery.FiniteLabelContinuation
variable {X : Type*} [LinearOrder X] {d : ℕ}
lemma select_card (loc : Fin d → X) (F Q : Finset X) : (select loc F Q F).card=F.card := by
  have h: (select loc F Q F).image (embed loc F Q)=F :=
    image_select loc F Q F (fun x hx=>(mem_alphabet loc F Q x).mpr (Or.inl hx))
  exact (Finset.card_image_of_injective (select loc F Q F) (embed loc F Q).injective).symm.trans (congrArg Finset.card h)
lemma complete_events (loc : Fin d → X) (distance : X → Fin d → ℚ) (F Q : Finset X) (v z lam : ℚ) :
    (complete loc distance F v z lam Q).length≤F.card ∧
      ∀ i∈complete loc distance F v z lam Q,i∈F := by
  obtain ⟨hn,hm⟩:=RationalPhase.completion_events (rows loc F Q distance) (select loc F Q F)
    (select loc F Q Q) v z lam
  refine ⟨by simpa only [complete,List.length_map,select_card] using hn,?_⟩
  intro i hi
  obtain ⟨j,hj,rfl⟩:=List.mem_map.mp hi
  exact (mem_select loc F Q F j).mp (hm j hj)
end MetricKMedianRecovery.FiniteLabelContinuation

end OAI
