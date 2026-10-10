import OAI.Combinatorics.HadwigerCounterexample.ExplicitStatusEquations

namespace OAI

/-! # Status Recipes -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Function LinearMap Module Submodule
open scoped BigOperators
namespace StatusAnalysis
variable {p : Shape} {n N : ℕ} {q : Format} {d e : Rates}
def registers {i : ℕ} (p : Shape) (j : Nodes) (v : Ax p n i) (m : Mixer p n)
    (x : UnitType p n N) : Profile p n→ₗ[F] Whole i where
  toFun z := ((role p n z,roll v (Tsym m z)),innerP p x j z)
  map_add' a b := by
    rw [map_add,map_add,map_add]; congr 1
  map_smul' a b := by
    rw [map_smul,map_smul,map_smul]; congr 1
def unionAt {p : Shape} {q : Format} (f : Messenger q → Profile p n) (i : Grid) :=
  ∑ j:Fin (q i), f ⟨i,j⟩

theorem funds_reg (t : Tagging p (Messenger q)) (b : Bool) (v : Charts p n d)
    (m : Mixer p n) (o : UnitType p n N) (l f x) (a : Amounts p q d b)
    (h : printed b v t l f m o x=a) (i : Grid) :
    let j := sendId b i
    let w := (manager b t l f).draw x
    funds a i = registers p j (v j) m o (unionAt (w.atomAt t) i) := by
  rw [←h]; intro j w
  unfold funds unionAt
  rw [map_sum]
  rfl

theorem sumAtSend (b : Bool) (w : Volley p n (Messenger q)) (t : Tagging p (Messenger q))
    (i : Grid) (h : w.obj=parcel b) :
    w.sumAt t (parcel (!b)) (sendId b i) (sendId (!b) i)=unionAt (w.atomAt t) i :=
  sum_shots b w _ h _

def owing (p : Shape) {q : Format} {d : Rates}
    (b : Bool) (a : Amounts p q d b) (u : Messenger q→ F) :=
  ∀ i,(a i).1.sumBit=u i

set_option maxHeartbeats 800000 in
theorem still_recipe (t : Tagging p (Messenger q)) (b : Bool) (S : Plan p n)
    (M : Cross p n) (v : Charts p n d) (ha : charted v S)
    (m : Mixer p n) (o : UnitType p n N) (l f x) (a : Amounts p q d b)
    (h : printed b v t l f m o x=a)
    (w : Volley p n (Messenger q)) (hw : w.obj=parcel (!b))
    (z : Messenger q→F) (hz : owing p b a z) (hq : ∀ i,fullq z i=1)
    (hh : still b a v M) :
    let u:=(manager b t l f).draw x
    u.scalarRecipe w t m o S M := by
  classical
  intro u
  have hi := funds_reg t b v m o l f x a h
  have ho : u.obj=parcel b := rfl
  have he (i j) (t : Grid) (h : t=transit b (i,j)) : sendId b t=i ∧ sendId (!b) t=j := by
    have hh := (sendPair b t).trans (show transit b t=(i,j) by rw [h,transit_inv])
    exact ⟨congrArg Prod.fst hh,congrArg Prod.snd hh⟩
  have ht (i j) : u.sumAt t w.obj i j=unionAt (u.atomAt t) (transit b (i,j)) := by
    obtain ⟨h1,h2⟩ := he i j _ rfl
    rw [hw,←sumAtSend b u t _ ho,h1,h2]
  have hd i j :
      ((innerP p o i)+role p n) (u.sumAt t w.obj i j)=
        couple _ (funds a (transit b (i,j))) := by
    rw [ht,hi]
    let W:= unionAt (u.atomAt t) (transit b (i,j))
    change innerP p o i W+role p n W=role p n W+innerP p o (sendId b _) W
    rw [(he _ _ _ rfl).1,add_comm]
  constructor
  · have hu (i) : u.diagonalAt i=z i :=
      (etaScan p (t i) (l i) (f i) (x i)).symm.trans (by
        rw [← h] at hz; exact hz i)
    intro i j
    obtain ⟨h1,h2⟩:= he i j _ rfl
    let T:= transit b (i,j)
    simp_rw [hu]
    have hm:=sum_shots b u (transit b (i,j)) ho z
    rw [h1,h2,←hw] at hm; exact hm.trans (hq T)
  · intro j; rw [hd,hd, hh.2]
  intro i j z hz
  let Z := transit b (i,j)
  obtain ⟨h1,h2⟩ : sendId b Z=i ∧ sendId (!b) Z=j := he _ _ _ rfl
  let t':=sendId b Z
  obtain ⟨y,hy⟩ : z ∈ LinearMap.range (v t') := by rw [(ha _).1]; rwa [show t'=i from h1]
  have hg := hh.1 Z
  rw [hi] at hg
  let W:= unionAt (u.atomAt t) Z
  have hh : Tsym m W z=contract p M i j z + role p n z := by
    change roll (v t') (Tsym m W)=roll (v t') (contract p M t' (sendId (!b) Z) + _) at hg
    have ht := congrArg (fun x=>dotProduct x y) hg
    simp_rw [←roll_project,hy] at ht
    change Tsym m W z=contract p M _ _ z+_ at ht
    rwa [show t'=i from h1,h2] at ht
  rw [ht,grad_val,hh,add_left_comm,char_two,add_zero]

end StatusAnalysis
end HadwigerCounterexample

end

end OAI
