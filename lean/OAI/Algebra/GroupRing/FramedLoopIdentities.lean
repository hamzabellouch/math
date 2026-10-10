import Mathlib
import OAI.Algebra.GroupRing.FramedConjugators
import OAI.Algebra.GroupRing.FramedSpherical
import OAI.Algebra.GroupRing.PathCharges

namespace OAI



section
namespace TorsionFreeZeroDivisors.FramedLoopIdentities
open scoped Classical BigOperators
open PortSubdivision GraphPresentation AlgebraicPictures InitialPicture WordFrames WordCursor
noncomputable section
variable {V D A I G M : Type} [Group G] [AddCommGroup M]
  (Γ : PortGraph V D) (label : D→A×Bool)
  (hl : ∀d,label (Γ.reverse d)=WordPairing.inverseLetter (label d))
  (rel : I→Loop Γ) (v : A×Bool→G)
  (hv : ∀a,v (WordPairing.inverseLetter a)=(v a)⁻¹)
  (c : G→D→M) (hc : ∀g d,c (g*v (label d)) (Γ.reverse d)=-c g d)
  (ts : List (Term (A:=A) (I:=I)))
def frames : List (G×List D) := ts.map (fun t=>(value v t.connector,(signedLoop Γ rel t).2.darts))
include hl in
lemma frames_labels : mapLabels label (frames Γ rel v ts)=framedCores v (relWords Γ label rel) ts := by
  simp only [mapLabels,frames,framedCores,List.map_map]
  apply List.map_congr_left
  intro t _
  apply Prod.ext
  · rfl
  · exact signedLoop_letters Γ label hl rel t
lemma frames_closed : WordBlocks.AllClosed Γ (words (frames Γ rel v ts)) := by
  intro w hw
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hw
  obtain ⟨t,_,rfl⟩ := List.mem_map.mp hb
  exact ⟨(signedLoop Γ rel t).1,(signedLoop Γ rel t).2,rfl⟩
def area (t : Term (A:=A) (I:=I)) : M :=
  PathCharges.charge (v∘label) c (value v t.connector) (signedLoop Γ rel t).2.darts
include hl hv hc in
/-- A free identity among conjugated closed relators has exactly zero lifted
edge area whenever sharp arrangement exclusion reduces all its actual spherical
pictures. The frames are not erased or existentially replaced. -/
theorem identity_area_zero
    (he : FreeGroup.mk (AlgebraicPictures.word (relWords Γ label rel) ts)=1)
    (ht : ∀t∈ts,value v (t.word (relWords Γ label rel))=1)
    (hred : ∀{O : Type}[Fintype O](a : SphericalPicture.Data (O:=O) Γ label WordPairing.inverseLetter),
      SphericalPicture.ReducesToEmpty Γ label WordPairing.inverseLetter a) :
    (ts.map (area Γ label rel v c)).sum=0 := by
  obtain ⟨d⟩ := identity_framed_cores v hv (relWords Γ label rel) ts he ht
  rw [←frames_labels Γ label hl rel v ts] at d
  have hh := WordFrames.charge_zero Γ d (frames_closed Γ rel v ts) hv hl c hc (hred _)
  rw [PathCharges.frames_sum] at hh
  simp only [frames,List.map_map] at hh
  exact hh
end
end TorsionFreeZeroDivisors.FramedLoopIdentities

end



end OAI
