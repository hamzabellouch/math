import OAI.Combinatorics.HadwigerCounterexample.ProductCoordinateReplacement
import OAI.Combinatorics.HadwigerCounterexample.MixerConditions

namespace OAI

/-! # Opposite Endpoint Forms -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix Module Finset Function Filter
variable {p : Shape} {n N : ℕ}

abbrev Notches (p : Shape) := Comp p.g × Bool

def duel (p : Shape) {n N : ℕ} (s t : Oframe p n N) (b : Bool) : Moment p n :=
  (primary (takeSign (p:=p) s b))ᵀ * primary (takeSign (p:=p) t (!b))

def duelPart (p : Shape) (c : Vec Bool) (x y : Oframe p n N) :=
  ∑ b:Bool,c b • duel p x y b
def issue (p : Shape) (c : Vec (Notches p)) (x : UnitType p n N) :=
  ∑ i:Comp p.g,duelPart p (fun b=>c (i,b)) (x.1 i) (x.2 i)

set_option maxHeartbeats 800000 in
theorem duel_live (p : Shape) :
    ∀ᶠ n : ℕ in atTop,∀ N : ℕ, 4*n≤ N → 2*num (Full p n)<N →
    ∀ (m : Mixer p n) (R S : Mat (Row p n) (Fin n)),
      Injective R.mulVec → Injective S.mulVec →
      ∀ (W : Mat (Fin n) (Fin n)) (c : Vec Bool), c true=1 →
      pr (pairW (rawC m N) (rawC m N))
        (fun x => 5*(pullM R S (duelPart p c x.1 x.2)+W).rank<n) ≤ bp (-(n:ℝ)*n/4) := by
  filter_upwards [paired_rank_scale]
    with n hn N hN hN' m R S hR hS W c hc
  let f := fun x : Oframe p n N => peer p R R x
  let g := fun x : Oframe p n N => peer p S S x
  let A := pullM R R (selfM p n m.mixM)
  let B := pullM S S (selfM p n m.mixM)
  let u := rawC m N
  have he (x y : Oframe p n N) : pullM R S (duelPart p c x y)+W =
      crossSquare n N W (c false) (f x,g y) := by
    unfold duelPart; rw [Fintype.sum_bool,map_add,map_smul,map_smul,hc,one_smul]
    unfold duel crossSquare f g peer; simp only [pullM_def,transpose_mul,Matrix.mul_assoc]
    exact add_assoc ..
  simp_rw [he]
  have h : mapW (pairW u u) (Prod.map f g) = pairW (unifOn (gramGood A)) (unifOn (gramGood B)) := by
    rw [map_pair_law]
    exact congrArg₂ pairW (peer_cap m N hN' hR hR) (peer_cap m N hN' hS hS)
  refine le_trans ?_ (hn N hN A B W (c false))
  rw [←h,mapW_pr]; exact le_rfl

theorem duel_turn (p : Shape) {n N : ℕ} (s t : Oframe p n N) (c : Vec Bool) :
    (duelPart p c s t)ᵀ= duelPart p (fun b => c (!b)) t s := by
  unfold duelPart duel; simp only [Fintype.sum_bool,transpose_add,transpose_mul,transpose_smul,
    transpose_transpose]; exact add_comm ..

set_option maxHeartbeats 800000 in
theorem duel_survives (p : Shape) :
    ∀ᶠ n : ℕ in atTop,∀ N : ℕ, 4*n≤ N → 2*num (Full p n)<N →
    ∀ (m : Mixer p n) (R S : Mat (Row p n) (Fin n)),
      Injective R.mulVec → Injective S.mulVec →
      ∀ (W : Mat (Fin n) (Fin n)) (c : Vec Bool), c≠0 →
      pr (pairW (rawC m N) (rawC m N))
        (fun x => 5*(pullM R S (duelPart p c x.1 x.2)+W).rank<n) ≤ bp (-(n:ℝ)*n/4) := by
  filter_upwards [duel_live p]
    with n hn N hN hN' m R S hR hS W c hc
  by_cases he : c true=1
  · exact hn N hN hN' m R S hR hS W c he
  have ht : c false=1 := by
    apply (bit_cases _).resolve_left
    intro h
    exact hc (funext fun i => by cases i; exact h; exact (bit_cases _).resolve_right he)
  let d := fun i:Bool => c (!i)
  have hh := hn N hN hN' m S R hS hR Wᵀ d ht
  let f (s t : Oframe p n N) := pullM R S (duelPart p c s t)+W
  have he (s t : Oframe p n N) :
      (f s t).rank = (pullM S R (duelPart p d t s)+Wᵀ).rank := by
    rw [← duel_turn (p:=p) s t c]
    simp only [pullM_def,f]
    have h : Sᵀ*(duelPart p c s t)ᵀ*R+Wᵀ=(f s t)ᵀ := by
      unfold f; simp only [pullM_def,transpose_add,transpose_mul,transpose_transpose,
        Matrix.mul_assoc]
    rw [h,Matrix.rank_transpose]
    rfl
  refine le_trans ?_ hh
  let u:=rawC m N
  change pr (pairW u u) (fun x => 5*(f x.1 x.2).rank<n)≤_
  simp_rw [he,pr,pairW_avg]
  rw [avg_avg]

set_option maxHeartbeats 1000000 in
theorem issue_live (p : Shape) :
    ∀ᶠ n : ℕ in atTop, ∀ N : ℕ, 4*n≤ N → 2*num (Full p n)<N →
    ∀ (m : Mixer p n) (s t : Label p.b) (c : Vec (Notches p)), c≠0 →
      let u := raw m N
      pr (pairW u u) (fun x => 5*blockRank Block.Z s t (issue p c x)<n) ≤
        bp (-(n:ℝ)*n/4) := by
  classical
  filter_upwards [duel_survives p] with n hn N hN hN' m s t c hc u
  obtain ⟨⟨j,b⟩,hb⟩ := Function.ne_iff.mp hc
  let f := fun i : Comp p.g => rawC m N
  let R := blockRay p n s Block.Z; let S:= blockRay p n t Block.Z
  let d := fun z : Bool => c (j,z)
  let F (x : UnitType p n N) := 5*(pullM R S (issue p c x)).rank < n
  have hd : d≠0 := fun h => hb (congr_fun h b)
  have hf i : IsLaw (f i) := unifOn_law (framesAt_exists (gramCond_exists m)
    (by rw [←two_mul]; simpa only [num,Fintype.card_fin] using hN'))
  have hU : IsLaw u := raw_law m hN'
  have hi (x : UnitType p n N) :
      pr (pairW (f j) (f j)) (fun y => F  (update x.1 j y.1,update x.2 j y.2))
        ≤ bp (-(n:ℝ)*n/4) := by
    let g := fun x : UnitType p n N => fun i =>
      duelPart p (fun b => c (i,b)) (x.1 i) (x.2 i)
    let W := pullM R S (∑ i∈univ.erase j,g x i)
    have he (y : Oframe p n N×Oframe p n N) :
        F (update x.1 j y.1,update x.2 j y.2) ↔
        5*(pullM R S (duelPart p d y.1 y.2) + W).rank<n := by
      unfold F issue W
      rw [← add_sum_erase _ _ (mem_univ j),map_add]; simp only [update_self]
      have h : ∑ i∈univ.erase j,g x i=∑ i∈univ.erase j,g (update x.1 j y.1,update x.2 j y.2) i :=
        sum_congr rfl fun i hi => by unfold g; simp only [update_of_ne ((mem_erase.mp hi).1)]
      rw [h]
    simp_rw [he]
    exact hn N hN hN' m R S (blockRay_inj ..) (blockRay_inj ..) W d hd
  change avg (pairW (prodW f) (prodW f)) (fun x => ind (F x))≤_
  rw [update2_avg f f j _ (hf j) (hf j)]
  exact (pairW_law hU hU).avg_le hi
end HadwigerCounterexample

end

end OAI
