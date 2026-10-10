import Mathlib
import OAI.Algebra.GroupRing.WordBlocksFurther

namespace OAI



section
namespace TorsionFreeZeroDivisors.WordBlocks
open scoped Classical
noncomputable section
variable {A G : Type} [Group G] {v : A→G} {inv : A→A} {ws vs : List (List A)}
def Lift.rename {d : Matching inv ws} (l : Lift v d) (e : Occ ws≃Occ vs)
    (hl : ∀x,letter vs (e x)=letter ws x)
    (hr : ∀x,e (BlockBoundary.rotation (lengths ws) x)=BlockBoundary.rotation (lengths vs) (e x)) :
    Lift v (d.rename e hl hr) where
  position i := l.position (e.symm i)
  next i := by
    obtain ⟨i,rfl⟩ := e.surjective i
    rw [←hr,Equiv.symm_apply_apply,Equiv.symm_apply_apply,hl]
    exact l.next i
  pair i := by
    obtain ⟨i,rfl⟩ := e.surjective i
    change l.position (e.symm (e.permCongr d.partner (e i)))=_
    simp only [Equiv.permCongr_apply,Equiv.symm_apply_apply,hl]
    exact l.pair i
variable (hv : ∀a,v (inv a)=(v a)⁻¹) (hinv : Function.Involutive inv)
variable (a : A) (w : List A) (ws : List (List A))
def capEmbedding (x : Occ (w::ws)) : Occ ((a::(w++[inv a]))::ws) :=
  (capCoordinates (inv:=inv) a w ws).symm (CyclicCaps.embed w.length x)
lemma capEmbedding_letter (x : Occ (w::ws)) :
    letter ((a::(w++[inv a]))::ws) (capEmbedding a w ws x)=letter (w::ws) x :=
  capLabel_embed a w ws x
variable {a w ws}
def Lift.removeCaps {d : Matching inv ((a::(w++[inv a]))::ws)} (l : Lift v d) :
    Lift v (d.removeCaps hinv a w ws) := by
  let e := capCoordinates (inv:=inv) a w ws
  let α := e.permCongr d.partner
  let σ := CyclicCaps.rotation w.length (BlockBoundary.rotation (lengths ws))
  let pos := fun x=>l.position (e.symm x)
  let lab := capLabel (inv:=inv) a w ws
  have hi : Function.Involutive α := PermutationTransport.involutive e d.partner d.involutive
  have hf : ∀x,α x≠x := PermutationTransport.fixed_free e d.partner d.fixed_free
  have hpos : ∀x,pos (σ x)=pos x*v (lab x) := by
    intro x
    have hs := capRotation (inv:=inv) a w ws
    change e.permCongr (BlockBoundary.rotation (lengths ((a::(w++[inv a]))::ws)))=σ at hs
    rw [←hs]
    change l.position (e.symm (e.permCongr _ x))=_
    simp only [Equiv.permCongr_apply,Equiv.symm_apply_apply]
    exact l.next _
  have hpair : ∀x,pos (α x)=pos x*v (lab x) := by
    intro x
    change l.position (e.symm (e.permCongr d.partner x))=_
    simp only [Equiv.permCongr_apply,Equiv.symm_apply_apply]
    exact l.pair _
  have hp : pos (CyclicCaps.q w.length)=pos (CyclicCaps.p w.length)*v (lab (CyclicCaps.p w.length)) := by
    rw [←CyclicCaps.next w.length (BlockBoundary.rotation (lengths ws))]
    exact hpos _
  have hq : pos (CyclicCaps.q w.length)*v (lab (CyclicCaps.q w.length))=pos (CyclicCaps.p w.length) := by
    rw [hp]
    dsimp only [lab]
    rw [capLabel_p,capLabel_q,hv,inv_mul_cancel_right]
  refine ⟨fun i=>l.position (capEmbedding a w ws i),?_,?_⟩
  · intro i
    have hh := Tightening.consistent σ (CyclicCaps.p w.length) (CyclicCaps.q w.length)
      (CyclicCaps.distinct w.length) (CyclicCaps.next _ _) pos (fun x=>pos x*v (lab x))
      (fun x=>(hpos x).symm) hq (CyclicCaps.coordinates w.length i)
    change pos (CyclicCaps.coordinates w.length i)*v (lab (CyclicCaps.coordinates w.length i))=
      pos (Tightening.rotation σ _ _ _ _ (CyclicCaps.coordinates w.length i)) at hh
    have rot := congrArg (fun x : MatchingSurgery.Remaining (CyclicCaps.p (R:=Occ ws) w.length)
      (CyclicCaps.q w.length)=>pos x)
      (CyclicCaps.rotation_commutes w.length (BlockBoundary.rotation (lengths ws)) i)
    have hh := rot.symm.trans hh.symm
    exact hh.trans (congrArg (pos (CyclicCaps.coordinates w.length i)*·)
      (congrArg v (capLabel_embed a w ws i)))
  · intro i
    change pos (CyclicCaps.coordinates w.length (CyclicCaps.partner w.length α hi hf i))=_
    change pos ((CyclicCaps.coordinates w.length) ((CyclicCaps.coordinates w.length).symm
      ((MatchingSurgery.partner α hi hf (CyclicCaps.p w.length) (CyclicCaps.q w.length)
        (CyclicCaps.distinct w.length)) (CyclicCaps.coordinates w.length i))))=_
    rw [Equiv.apply_symm_apply]
    change pos (PartialMatchingSurgery.splice α (CyclicCaps.p w.length) (CyclicCaps.q w.length)
      (CyclicCaps.coordinates w.length i))=_
    let x := CyclicCaps.coordinates w.length i
    have hh : pos (PartialMatchingSurgery.splice α (CyclicCaps.p w.length) (CyclicCaps.q w.length) x)=pos x*v (lab x) := by
      by_cases h1 : α x=CyclicCaps.p w.length
      · rw [PartialMatchingSurgery.splice,ite_eq_left h1,hpair,hq]
        exact (congrArg pos h1).symm.trans (hpair x)
      · by_cases h2 : α x=CyclicCaps.q w.length
        · rw [PartialMatchingSurgery.splice,ite_eq_right h1,ite_eq_left h2,hpair,←hp]
          exact (congrArg pos h2).symm.trans (hpair x)
        · rw [PartialMatchingSurgery.splice,ite_eq_right h1,ite_eq_right h2,hpair]
    exact hh.trans (congrArg (pos x*·) (congrArg v (capLabel_embed a w ws i)))
end
end TorsionFreeZeroDivisors.WordBlocks

end


end OAI
