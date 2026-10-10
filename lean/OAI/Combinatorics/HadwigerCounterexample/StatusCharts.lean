import OAI.Combinatorics.HadwigerCounterexample.FourEdgeFamilies
import OAI.Combinatorics.HadwigerCounterexample.PredictionExactification

namespace OAI

/-! # Status Charts -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Function Module LinearMap Submodule
open scoped BigOperators

namespace StatusAnalysis
abbrev Ax (p : Shape) (n : ℕ) (d : ℕ) := Cell d→ₗ[F] Profile p n
abbrev Charts (p : Shape) (n : ℕ) (d : Rates) := ∀ i, Ax p n (d i)
variable {p : Shape} {n N : ℕ} {d e : Rates}
def charted (v : Charts p n d) (w : Plan p n) :=
  ∀ i,LinearMap.range (v i)=effective w i ∧ Injective (v i)

theorem chart_create (p : Shape) (n : ℕ) (w : Plan p n) :
    let d:= fun i:Nodes=> dim (effective w i)
    ∃ v : Charts p n d,charted v w := by
  classical
  intro d
  have hh (i) :
      ∃ f : Ax p n (d i),LinearMap.range f=effective w i ∧ Injective f := by
    let S:= effective w i
    let E : Cell (d i)≃ₗ[F] S := LinearEquiv.ofFinrankEq _ _
      (by change dim (Cell (d i))=d i; rw [dim_vec,Fintype.card_fin])
    refine ⟨S.subtype ∘ₗ E.toLinearMap,?_,Subtype.val_injective.comp E.injective⟩
    rw [LinearMap.range_comp,LinearMap.range_eq_top.mpr E.surjective,← LinearMap.range_eq_map,
      Submodule.range_subtype S]
  choose f h using hh
  exact ⟨f,h⟩

abbrev Format := Grid→ℕ
abbrev Messenger (q : Format) := Σ i:Grid,Fin (q i)
def sendId (b : Bool) (i : Grid) := if b then i.1 else i.2
def transit (b : Bool) (q : Grid) := if b then q else (q.2,q.1)
theorem sendPair (b : Bool) (x : Grid) :
    (sendId b x,sendId (!b) x)=transit b x := by cases b <;> rfl
theorem transit_inv (b : Bool) (x : Grid) : transit b (transit b x)=x := by cases b <;> rfl

def parcel (b : Bool) {q : Format} (x : Messenger q) := sendId b x.1
def manager {q : Format} (b : Bool) (t : Tagging p (Messenger q)) (s : Messenger q→Label p.b)
    (f : Messenger q→Flavor p.g) : Template p (Messenger q) := ⟨parcel b,t,s,f⟩

def roll {u : ℕ} (f : Ax p n u) (g : Pdual p n) : Cell u := fun i=>g (f (Pi.single i 1))

theorem roll_project {u : ℕ} (f : Ax p n u) (g : Pdual p n) (z : Cell u) :
    g (f z)=dotProduct (roll f g) z := by
  let h:=g ∘ₗ f
  obtain ⟨x,hx⟩:=dotL_surj h
  have hi (i:Fin u) :
      roll f g i=x i := by
    change h (Pi.single i 1)=_
    rw [hx]; change dotProduct x (Pi.single i 1)=x i
    simp
  rw [show roll f g=x from funext hi]
  exact LinearMap.congr_fun hx z

def targetMark (p : Shape) (v : Charts p n d) (M : Cross p n) (i j : Nodes) : Cell (d i) :=
  roll (v i) (contract p M i j + role p n)
def hailing (p : Shape) (v : Charts p n d) (z : Charts p n e) (M : Cross p n) :
    Cabinet d e :=
  fun i => (1,1,targetMark p v M i.1 i.2,targetMark p z (reciprocal p M) i.2 i.1)

abbrev Magazine (p : Shape) (d : ℕ) := Digest p.g × Whole d
def specify (p : Shape) {d : ℕ} (i : Nodes) (v : Ax p n d)
    (m : Mixer p n) (o : UnitType p n N) (l : Tag p.g) (s : Label p.b) (f : Flavor p.g)
    (x : Knobs p.g n) : Magazine p d :=
  let A:=useAtom p l s f x
  (scan p l f x, (role p n A,roll v (Tsym m A)),innerP p o i A)

variable {q : Format}

def printed (b : Bool) (v : Charts p n d) (t : Tagging p (Messenger q))
    (s : Messenger q →Label p.b) (f : Messenger q → Flavor p.g) (m : Mixer p n)
    (o : UnitType p n N) (x : Inputs p n (Messenger q)) :=
  fun i => specify p (parcel b i) (v (parcel b i)) m o (t i) (s i) (f i) (x i)
abbrev Amounts (p : Shape) (q : Format) (d : Rates) (b : Bool) :=
    ∀ i:Messenger q,Magazine p (d (parcel b i))
def sendSum (u : Messenger q→F) (a : Amounts p q d true) (b : Amounts p q e false) :
    ∀ i : Grid, Suite d e i :=
  fun i=> ∑ j:Fin (q i), (u ⟨i,j⟩,(a ⟨i,j⟩).2,(b ⟨i,j⟩).2)

set_option maxHeartbeats 600000 in
theorem shooting_range (b : Bool) (v : Volley p n (Messenger q)) (x : Grid)
    (h : v.obj = parcel b) :
    v.shoots (parcel (!b)) (sendId b x) (sendId (!b) x) =
      univ.image (fun i:Fin (q x)=> Sigma.mk x i) := by
  classical
  ext i; unfold Volley.shoots
  rw [h]; rcases i with ⟨j,i⟩
  constructor
  · intro hh
    have he := (mem_filter.mp hh).2
    have ht : transit b j=transit b x := by
      rw [←sendPair,←sendPair]; exact Prod.ext he.1 he.2
    have hh : j=x := by rw [←transit_inv b j,ht,transit_inv]
    subst j; exact mem_image.mpr ⟨i,mem_univ _,rfl⟩
  intro h
  obtain ⟨k,_,hh⟩:= mem_image.mp h
  rw [← hh]; exact mem_filter.mpr ⟨mem_univ _,rfl,rfl⟩

variable {H : Type} [AddCommMonoid H]
theorem sum_shots (b : Bool) (v : Volley p n (Messenger q)) (x : Grid)
    (h : v.obj=parcel b) (u : Messenger q→ H) :
    (∑ j∈v.shoots (parcel (!b)) (sendId b x) (sendId (!b) x),u j) =
      ∑ i:Fin (q x),u ⟨x,i⟩ := by
  classical
  rw [shooting_range b _ _ h,Finset.sum_image]
  exact (fun x hx y hy e=> Sigma.mk.inj_iff.mp e |>.2 |> eq_of_heq)

theorem shots_ok {q : Format} (b : Bool) (v : Volley p n (Messenger q))
    (h : v.obj=parcel b) (hh : ∀ i,1≤q i∧q i≤7) :
    v.bounded (parcel (!b)) := by
  intro x y
  let i:= transit b (x,y)
  have he : sendId b i=x := congrArg Prod.fst ((sendPair b i).trans (transit_inv b _))
  have hg : sendId (!b) i=y := congrArg Prod.snd ((sendPair b i).trans (transit_inv b _))
  have ht : (v.shoots (parcel (!b)) x y).card = q i := by
    rw [←he,←hg,shooting_range b v i h, card_image_of_injective,card_univ,Fintype.card_fin]
    exact fun i j he=> Sigma.mk.inj_iff.mp he |>.2 |> eq_of_heq
  change 1≤_∧_≤7; rw [ht]
  exact hh i
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
