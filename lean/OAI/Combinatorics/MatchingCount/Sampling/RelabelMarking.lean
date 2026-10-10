import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.Relabel

namespace OAI

namespace MatchingFPRAS.Transport
open Finset

variable {V E F I : Type*} [Fintype V] [DecidableEq V]
variable [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F] [Fintype I]
variable {inc : E → V → Prop} {j : F → V → Prop}
def selectedEquiv (e : E ≃ F) (he : ∀ a v,j (e a) v ↔ inc a v) (M : PM inc) :
    ↥M.val ≃ ↥(pmEquiv e he M).val where
  toFun a:=⟨e a.val,mem_image.mpr ⟨a.val,a.property,rfl⟩⟩
  invFun a:=⟨e.symm a.val,by
    obtain ⟨b,hb,heq⟩:=mem_image.mp a.property
    simpa [←heq] using hb⟩
  left_inv a:=by apply Subtype.ext; exact e.symm_apply_apply _
  right_inv a:=by apply Subtype.ext; exact e.apply_symm_apply _
def markedEquiv (e : E ≃ F) (he : ∀ a v,j (e a) v ↔ inc a v) :
    Marking.Marked (I:=I) inc ≃ Marking.Marked (I:=I) j :=
  Equiv.sigmaCongr (pmEquiv e he) (fun M=>Equiv.arrowCongr (selectedEquiv e he M) (Equiv.refl I))
omit [DecidableEq V] [Fintype E] [Fintype F] [Fintype I] in
lemma markedEquiv_fst (e : E ≃ F) (he : ∀ a v,j (e a) v ↔ inc a v)
    (a : Marking.Marked (I:=I) inc) : (markedEquiv e he a).1=pmEquiv e he a.1 := rfl
omit [DecidableEq V] [Fintype E] [Fintype F] [Fintype I] in
lemma markedEquiv_mark (e : E ≃ F) (he : ∀ a v,j (e a) v ↔ inc a v)
    (a : Marking.Marked (I:=I) inc) (x : a.1.val) :
    (markedEquiv e he a).2 (selectedEquiv e he a.1 x)=a.2 x := by
  change a.2 ((selectedEquiv e he a.1).symm (selectedEquiv e he a.1 x))=a.2 x
  rw [Equiv.symm_apply_apply]
omit [DecidableEq V] [Fintype E] [Fintype F] [Fintype I] in
lemma mass_markedEquiv (e : E ≃ F) (he : ∀ a v,j (e a) v ↔ inc a v)
    (part : F → I → ℝ) (a : Marking.Marked (I:=I) inc) :
    Marking.mass j part (markedEquiv e he a)=Marking.mass inc (part ∘ e) a := by
  apply Fintype.prod_equiv (selectedEquiv e he a.1).symm
  intro x
  change part x.val ((markedEquiv e he a).2 x)=part (e ((selectedEquiv e he a.1).symm x).val) (a.2 ((selectedEquiv e he a.1).symm x))
  rw [←markedEquiv_mark e he a]
  simp only [Equiv.apply_symm_apply]
  congr 1
  exact (e.apply_symm_apply x.val).symm
lemma partitionWeight_pmEquiv (e : E ≃ F) (he : ∀ a v,j (e a) v ↔ inc a v)
    (w : F → ℝ) : partitionWeight j w univ=partitionWeight inc (w ∘ e) univ := by
  classical
  unfold partitionWeight
  symm
  apply Fintype.sum_equiv (pmEquiv e he)
  intro M
  exact (matchingWeight_pmEquiv e he w M).symm
lemma law_markedEquiv (e : E ≃ F) (he : ∀ a v,j (e a) v ↔ inc a v)
    (part : F → I → ℝ) (a : Marking.Marked (I:=I) inc) :
    Marking.law j part (markedEquiv e he a)=Marking.law inc (part ∘ e) a := by
  unfold Marking.law
  rw [mass_markedEquiv,partitionWeight_pmEquiv e he]
  rfl
end MatchingFPRAS.Transport

end OAI
