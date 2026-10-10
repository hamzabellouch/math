import Mathlib
import OAI.Algebra.GroupRing.ConePicture

namespace OAI



section
namespace TorsionFreeZeroDivisors.PictureChains
open scoped Classical BigOperators
open SphericalPicture PortSubdivision
noncomputable section
variable {V D A G M : Type} [Group G] [AddCommGroup M]
  (Γ : PortGraph V D) (label : D→A) (inv : A→A) (eval : A→G)
  (heval : ∀a,eval (inv a)=(eval a)⁻¹)
  (hlabel : ∀d,label (Γ.reverse d)=inv (label d))
variable {O : Type} [Fintype O] (a : Data (O:=O) Γ label inv)
/-- The actual group-coordinate lift of every boundary occurrence. Rotation
and paired sides share the prescribed endpoint in the Cayley one-skeleton. -/
structure Lift where
  position : O→G
  next : ∀i,position (a.rotation i)=position i*eval (label (a.dart i))
  pair : ∀i,position (a.partner i)=position i*eval (label (a.dart i))
variable {Γ label inv eval} (l : Lift Γ label inv eval a)
include heval hlabel in
lemma reverse_value (d : D) : eval (label (Γ.reverse d))=(eval (label d))⁻¹ := by
  rw [hlabel,heval]
include heval hlabel in
lemma inverse_segment {p q : O} (hpos : l.position q=l.position p*eval (label (a.dart p)))
    (he : a.dart q=Γ.reverse (a.dart p)) :
    l.position q*eval (label (a.dart q))=l.position p := by
  rw [hpos,he,reverse_value heval hlabel,mul_inv_cancel_right]
variable (p q : O) (hpq : p≠q)
def band (hpair : a.partner p=q) (he : a.dart q=Γ.reverse (a.dart p)) :
    Lift Γ label inv eval (a.band p q hpq hpair he) where
  position i := l.position (BandEuler.val p q hpq i)
  next i := (BoundarySurgery.consistent a.rotation l.position
    (fun j=>l.position j*eval (label (a.dart j))) p q hpq
    (fun i=>(l.next i).symm)
    (by rw [←l.pair,hpair])
    (inverse_segment heval hlabel a l (by rw [←hpair,l.pair]) he) i).symm
  pair i := by
    change l.position (BandEuler.val p q hpq (BandEuler.partner a.partner a.involutive p q hpq hpair i))=_
    rw [BandEuler.partner_val]
    exact l.pair _
def tighten (hinv : Function.Involutive inv) (hsp : a.rotation p=q)
    (he : a.dart q=Γ.reverse (a.dart p)) :
    Lift Γ label inv eval (a.tighten p q hpq hinv hlabel hsp he) where
  position i := l.position i
  next i := (Tightening.consistent a.rotation p q hpq hsp l.position
    (fun j=>l.position j*eval (label (a.dart j))) (fun i=>(l.next i).symm)
    (inverse_segment heval hlabel a l (by rw [←hsp,l.next]) he) i).symm
  pair i := by
    change l.position (PartialMatchingSurgery.splice a.partner p q i)=_
    by_cases h1 : a.partner i=p
    · rw [PartialMatchingSurgery.splice,ite_eq_left h1,l.pair]
      exact (inverse_segment heval hlabel a l (by rw [←hsp,l.next]) he).trans
        ((congrArg l.position h1).symm.trans (l.pair i))
    · by_cases h2 : a.partner i=q
      · rw [PartialMatchingSurgery.splice,ite_eq_right h1,ite_eq_left h2,l.pair]
        exact (l.next p).symm.trans ((congrArg l.position hsp).trans
          ((congrArg l.position h2).symm.trans (l.pair i)))
      · rw [PartialMatchingSurgery.splice,ite_eq_right h1,ite_eq_right h2]
        exact l.pair i

variable (c : G→D→M)
  (hc : ∀g d,c (g*eval (label d)) (Γ.reverse d)=-c g d)
def chain : M := ∑i,c (l.position i) (a.dart i)
include hc in
lemma cancel_pair {p q : O} (hpos : l.position q=l.position p*eval (label (a.dart p)))
    (he : a.dart q=Γ.reverse (a.dart p)) :
    c (l.position p) (a.dart p)+c (l.position q) (a.dart q)=0 := by
  rw [hpos,he,hc,add_neg_cancel]

lemma sum_remaining {B : Type*} [AddCommGroup B] {O : Type*} [Fintype O]
    (p q : O) (hpq : p≠q) (f : O→B) (hf : f p+f q=0) :
    (∑i : PartialMatchingSurgery.Remaining p q,f i)=∑i,f i := by
  classical
  have hs : (∑i∈Finset.univ.erase p |>.erase q,f i)+f q+f p=∑i,f i := by
    rw [Finset.sum_erase_add _ _ (by simp [hpq.symm]),Finset.sum_erase_add _ _ (Finset.mem_univ _)]
  have hsum : (∑i : PartialMatchingSurgery.Remaining p q,f i)=
      ∑i∈Finset.univ.erase p |>.erase q,f i := by
    apply Finset.sum_bij (fun i _=>i.1)
    · intro i _;simp only [Finset.mem_erase,Finset.mem_univ,and_true];exact ⟨i.2.2,i.2.1⟩
    · intro i _ j _ hij;exact Subtype.ext hij
    · intro j hj
      simp only [Finset.mem_erase,Finset.mem_univ,and_true] at hj
      exact ⟨⟨j,hj.2,hj.1⟩,Finset.mem_univ _,rfl⟩
    · intro i _;rfl
  rw [hsum]
  have hh : f q+f p=0 := by rwa [add_comm] at hf
  simpa only [add_assoc,hh,add_zero] using hs

include hc in
lemma band_chain (hpair : a.partner p=q) (he : a.dart q=Γ.reverse (a.dart p)) :
    chain (a.band p q hpq hpair he) (band heval hlabel a l p q hpq hpair he) c=chain a l c := by
  change (∑i : BandEuler.Residual p q hpq,c (l.position (BandEuler.val p q hpq i)) (a.dart (BandEuler.val p q hpq i)))=_
  exact ((Data.deletionCoordinates p q hpq).sum_comp
    (fun i : PartialMatchingSurgery.Remaining p q=>c (l.position i) (a.dart i))).trans
    (sum_remaining p q hpq (fun i=>c (l.position i) (a.dart i))
      (cancel_pair a l c hc (by rw [←hpair,l.pair]) he))
include hc in
lemma tighten_chain (hinv : Function.Involutive inv) (hsp : a.rotation p=q)
    (he : a.dart q=Γ.reverse (a.dart p)) :
    chain (a.tighten p q hpq hinv hlabel hsp he) (tighten heval hlabel a l p q hpq hinv hsp he) c=chain a l c := by
  change (∑i : PartialMatchingSurgery.Remaining p q,c (l.position i) (a.dart i))=_
  exact sum_remaining p q hpq (fun i=>c (l.position i) (a.dart i))
    (cancel_pair a l c hc (by rw [←hsp,l.next]) he)

include heval hlabel hc in
/-- Every actual lifted genus-zero spherical boundary picture which reduces as
proved by the sharp arrangement exclusion has ZERO integral cell-chain charge.
Only an antisymmetric physical cone-edge contribution is needed. -/
theorem chain_eq_zero (h : ReducesToEmpty Γ label inv a) : chain a l c=0 := by
  induction h with
  | empty a h =>
    let := h
    simp only [chain, Finset.univ_eq_empty, Finset.sum_empty]
  | band a p q hpq hpair he next ih =>
    rw [←band_chain heval hlabel a l p q hpq c hc hpair he]
    exact ih (band heval hlabel a l p q hpq hpair he)
  | tighten a p q hpq hinv hl hsp he next ih =>
    rw [←tighten_chain heval hl a l p q hpq c hc hinv hsp he]
    exact ih (tighten heval hl a l p q hpq hinv hsp he)
end
end TorsionFreeZeroDivisors.PictureChains

end


end OAI
