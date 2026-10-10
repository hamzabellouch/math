import OAI.Combinatorics.HadwigerCounterexample.SinglePositionExpansion

namespace OAI

/-! # Four Corner Masks -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Filter Function
open scoped BigOperators
variable {p : Shape} {I : Type} [Fintype I] [DecidableEq I] {n N : ℕ}

def wingpair (I : Type) : (Bool→ I)≃ I × I where
  toFun x := (x true,x false)
  invFun x := onSide x
  left_inv i := by funext j; cases j <;> rfl
  right_inv _ := rfl

namespace Template
variable (v : Template p I)
abbrev PackSlot (v : Template p I) := Bool × KeySlots p v.t

abbrev PackStack (v : Template p I) (N : ℕ) := Rack v.PackSlot N

def untwin (v : Template p I) (N) :
    v.PackStack N ≃ Keys (p:=p) v.t N × Keys (p:=p) v.t N :=
  let E:=scatter v.t N
  ((relay Bool (KeySlots p v.t) N).trans (wingpair _)).trans (E.symm.prodCongr E.symm)

def yieldK (v : Template p I) (j : I) (c : Corn) (x : v.PackStack N) :=
  criss (v.chairK j N) (v.untwin N x) c
def seam (v : Template p I) : Route v.PackSlot (Ports p) := tied (globPort p v.t v.aim) Bool

def sees (v : Template p I) (j : I) (c : Corn) (w : v.PackSlot) :=
  arm j w.2.1 c=w.1
instance (v : Template p I) (j c w) : Decidable (sees v j c w) := Classical.propDecidable _

def cantRail (v : Template p I) (j : I) := open Classical in
  (crowded v.seam).filter (fun x => ¬∃ c,sees v j c x.1 ∧ sees v j c x.2)

theorem cant_mem (v : Template p I) (j) (x) :
    x∈cantRail v j ↔ x∈crowded v.seam ∧ ¬∃ c,sees v j c x.1 ∧ sees v j c x.2 := mem_filter

def cantVec (v : Template p I) (j : I) (Z : GeoM v.seam) : Vec (cantRail v j) :=
  fun x => directions _ Z ⟨x.val,((cant_mem ..).mp x.property).1⟩

theorem yield_view (v : Template p I) (j) (c : Corn) (x : v.PackStack N)
    (i : v.PackSlot) (he : sees v j c i) (b : Bool) (z : Fin N) :
    yieldK v j c x i.2.1 i.2.2 b z= if b then x.1 z i else x.2 z i := by
  classical
  have hh : yieldK v j c x i.2.1=onSide (v.untwin N x) i.1 i.2.1 := by
    have hg := chair_arm (X:=fun i=>AtomKey (p:=p) (v.t i) N) (v.untwin N x) j i.2.1 c
    rw [show arm j i.2.1 c=i.1 from he] at hg
    exact hg
  rw [hh]
  cases i with | mk r y => cases r <;> cases b <;> rfl

theorem scores_together (v : Template p I) (j : I) (c : Corn) (x : v.PackStack N)
    (i k : v.PackSlot) (he : sees v j c i) (hk : sees v j c k) :
    scoreR x i k=scoreR (scatter v.t N (yieldK v j c x)) i.2 k.2 := by
  classical
  have h z : (scatter v.t N (yieldK v j c x)).1 z i.2=x.1 z i := yield_view v j c x i he true z
  have hh z : (scatter v.t N (yieldK v j c x)).2 z k.2=x.2 z k := yield_view v j c x k hk false z
  unfold scoreR; simp only [Matrix.mul_apply,transpose_apply,h,hh]

omit [Fintype I] in
theorem seam_score_fixed (v : Template p I) (q : I→F) (x y : Keys (p:=p) v.t N)
    (hx : ownPart (p:=p) v.t q x) (hy : ownPart (p:=p) v.t q y) (a b : v.PackSlot)
    (h : v.seam a=v.seam b) :
    scoreR (scatter v.t N x) a.2 b.2=scoreR (scatter v.t N y) a.2 b.2 := by
  have ht : ownPort (p:=p) v.t a.2 = ownPort (p:=p) v.t b.2 := congrArg Prod.snd h
  let c := ownPort (p:=p) v.t a.2
  let i : Port (ownPort (p:=p) v.t) c := ⟨a.2,rfl⟩
  let j : Port (ownPort (p:=p) v.t) c := ⟨b.2,ht.symm⟩
  exact ((part_scores (scatter v.t N x) (ownMap (p:=p) v.t q)).mp hx c i j).trans
    (((part_scores ..).mp hy c i j).symm)

def gatedStack (v : Template p I) (j : I) (q : I→F) (x : v.PackStack N) :=
  ∀ i:Corn,ownPart (p:=p) v.t q (yieldK v j i x)

theorem cant_bridge (v : Template p I) (j : I) (q : I→F)
    (Z : GeoM v.seam) (x y : v.PackStack N) (hx : gatedStack v j q x)
    (hy : gatedStack v j q y) (he : gramPart Z x) :
    gramPart Z y ↔ traced y (cantRail v j) (cantVec v j Z) := by
  classical
  constructor
  · intro hh
    funext i
    exact congr_fun ((match_crowd y _ Z).mpr hh)
      (⟨i.val,((cant_mem ..).mp i.property).1⟩ : ↑(crowded v.seam))
  intro ht
  refine (part_scores y Z).mpr fun i a b => ?_
  have hb : v.seam a.val=v.seam b.val := a.property.trans b.property.symm
  have hi : (a.val,b.val)∈crowded v.seam := Finset.mem_filter.mpr ⟨mem_univ _,hb⟩
  rcases a with ⟨a,ha⟩; rcases b with ⟨b,hb'⟩
  subst i
  by_cases hg : ∃ c, sees v j c a ∧ sees v j c b
  · obtain ⟨c,hC,hB⟩ := hg
    have hh : scoreR y a b=scoreR x a b := by
      rw [scores_together v j c y a b hC hB,scores_together v j c x a b hC hB]
      exact seam_score_fixed v q _ _ (hy c) (hx c) a b hb
    exact hh.trans ((part_scores x Z).mp he _ ⟨a,rfl⟩ ⟨b,hb'⟩)
  have hh : (a,b)∈cantRail v j := (cant_mem ..).mpr ⟨hi,hg⟩
  exact congr_fun ht (⟨(a,b),hh⟩ : ↑(cantRail v j))

def packSecs (v : Template p I) (j : I) (U : Wgt (Keys (p:=p) v.t N)) (x : v.PackStack N) :=
  ∏ i:Corn,U (yieldK v j i x)

theorem pack_gate (v : Template p I) (j : I) (q : I→ F) {x : v.PackStack N}
    (U : Wgt (Keys (p:=p) v.t N)) (h : carried U (ownPart (p:=p) v.t q))
    (hx : packSecs v j U x≠0) :
    gatedStack v j q x :=
  fun i=> by_contra (fun he => hx (Finset.prod_eq_zero (mem_univ i) (h (yieldK v j i x) he)))

end Template
end HadwigerCounterexample

end

end OAI
