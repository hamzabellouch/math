import OAI.Combinatorics.HadwigerCounterexample.NumericalGramPrescriptions

namespace OAI

/-! # Zero Discrepancy Prediction -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Module LinearMap Submodule Function
open scoped BigOperators
variable {p : Shape} {n N : ℕ}
def zoomset (p : Shape) (w : Tag p.g →Moment p n) :=
    Finset.univ.filter (fun i => etab p n Block.S (w i)≠0)

theorem zoom_le (w : Tag p.g → Moment p n) : (zoomset p w).card≤ (nonzeroTags w).card := by
  apply Finset.card_le_card
  intro i hi
  exact (mem_nonzeroTags i w).mpr (fun he => (mem_filter.mp hi).2 (by rw [he,map_zero]))

def screenRank (p : Shape) (K : ℕ) := (p.g-1)*(p.h+2*p.J*K)
def screen (p : Shape) (i : Orient p n N) (s : Label p.b) (E : Finset (Tag p.g)) (r : ℕ)
    (g : Augur p N) (δ : ℝ) :=
  ∃ w : Pdual p n,
    (∀ l f,pr (spins p n) (mismatch p g w l s f i) ≤ δ)∧
    ∀ l : Tag p.g,
    ∃ M:Moment p n,M.rank ≤ r ∧ ∀ x : Knobs p.g n,
      let f:= creed p E
      let v:=spring p l s f x
      w (useAtom p l s f x)=dialed p l f x+evmat M v v

set_option maxHeartbeats 600000 in
theorem coreRole (p : Shape) (w : Tag p.g→Moment p n) (hw : ∀ t,w t∈Wtag p n t)
    (α : F) (hg : Odd p.g) (h : parityW w+α=1) (l s x) :
    let f:= creed p (zoomset p w)
    let M:=useAtom p l s f x
    T0 p n (cut p n w) M + α*role p n M=dialed p l f x := by
  classical
  intro f M
  let U:=cut p n w
  let Q:= scan p l f x
  have h1 : Q (.inr ())=0 := by simp [Q,f,scan,creed,Flavor.keeps,asBlock,Block.S]
  have hq : role p n M=dialed p l f x := by
    rw [role_scan]
    change Q.diagO=Q.sumBit; unfold Digest.sumBit; rw [h1,add_zero]
  let E:=zoomset p w
  have hh t : sharedT p n t M=0 := by rw [sharedT_scan p hg]; change Q _+(if l=t then Q _ else 0)=_
                                           ; rw [h1]; simp
  have he t (ht : t∈ E) : roleT p n t M=0 := by
    rw [roleT_scan p]
    refine sum_eq_zero fun i _ => ?_
    have hv : ¬ f.keeps l (Block.O i t) := fun hx=> (mem_filter.mp hx.2).2 ht
    unfold scan; exact ite_eq_right hv
  have hl t (hE : t∉E) :
      role p n U+sharedT p n t U+α=1 := by
    have hz : etab p n Block.S (w t)=0 := not_ne_iff.mp (fun hg=>hE (mem_filter.mpr ⟨mem_univ _,hg⟩))
    unfold U
    rw [role_cut p w hw,sharedT_cut p hg t,hz,add_zero,← Finset.sum_add_distrib]
    exact h
  rw [T0_val]; change role _ _ U* _ + _ + _ = _
  simp_rw [hh,mul_zero,zero_add]
  rw [←hq]
  let r := role p n U
  have hm : role p n M=∑ t, roleT p n t M := by unfold role; rw [LinearMap.sum_apply]
  rw [hm,mul_sum,mul_sum,←sum_add_distrib,←sum_add_distrib]
  refine Finset.sum_congr rfl fun t _=>?_
  by_cases ht : t∈E
  · rw [he t ht]; ring
  rw [← add_mul,←add_mul,hl t ht,one_mul]

theorem inner_gem (p : Shape) (x : UnitType p n N) (i : Bool) (t : Tag p.g) :
    ∃ M : Moment p n,M.rank ≤ (p.g-1)*p.h ∧ ∀ (s z),
      innerP p x i (atom p t s z)=mpair M (mom p s z) := by
  classical
  let A:=onSide x i; let B:=onSide x (!i)
  let P (e : Comp p.g) := channel (B e).2*(channel (B e).1)ᵀ
  let Z (e : Comp p.g) := liftM (primary (A e).1)ᵀ (primary (A e).2)ᵀ (P e)
  let M := ∑ i:TagStar t,Z i.val
  have ht i : (Z i).rank ≤ p.h := (rank_lift_le ..).trans ((Matrix.rank_mul_le_left ..).trans
    ((Matrix.rank_le_card_width (channel (B i).2)).trans_eq (by simp)))
  refine ⟨M,(mrk_sum_le ..).trans ((Finset.sum_le_sum (fun i _=>ht i.val)).trans_eq ?_),?_⟩
  · simp only [sum_const,card_univ,nsmul_eq_mul,Nat.cast_id,card_star]
  intro s z
  change (∑ i:Comp p.g, mpair (P i) (liftM (primary (A i).1) (primary (A i).2) (atom p t s z i)))
    =_
  let Q:= mom p s z
  have he i :
      mpair (P i) (liftM (primary (A i).1) (primary (A i).2) (atom p t s z i)) =
      if inc i t then mpair (Z i) Q else 0 := by
    rw [mpair_liftM,atom_def]; by_cases ht:inc i t <;> simp only [ht,ite_false,ite_true,map_zero]; rfl
  simp_rw [he]
  unfold M; rw [←Finset.sum_filter,mpair_sum]; exact Finset.sum_subtype _ (by simp) _

theorem zero_screen (p : Shape) (x : UnitType p n N) (i : Bool) (s : Label p.b)
    (m : Mixer p n) (α : F) (hg : Odd p.g)
    (w : Tag p.g→Moment p n) (hw : ∀ i,w i∈ Wtag p n i) (h : parityW w+α=1)
    (K : ℕ) (hk : totalRank (cut p n w) ≤ K) (g : Augur p N)
    (δ : ℝ) (L : Finset (Label p.b)) (hs : s∉ L)
    (hz : postulates p (onSide x i) g (yoke p m x i (cut p n w) α) L δ) :
    screen p (onSide x i) s (zoomset p w) (screenRank p K) g δ := by
  classical
  let a := cut p n w; let f:=creed p (zoomset p w)
  refine ⟨_,hz s hs,fun l=>?_⟩
  obtain ⟨M,hM,ht⟩:=inner_gem p x i l
  refine ⟨M+qmix m a l,le_trans (mrk_add_le ..) ?_,fun y=>?_⟩
  · refine (Nat.add_le_add hM (qmix_rank ..)).trans ?_
    unfold screenRank; change _+p.J*(p.g-1)*(2*totalRank a)≤_
    exact le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left (p.J*(p.g-1))
      (Nat.mul_le_mul_left 2 hk)) _) (le_of_eq (by ring))
  let A:=useAtom p l s f y
  let z:=lit f l y; let T:=mom p s z
  have h0 : (Tsym m a+α • role p n) A= dialed p l f y+mpair (qmix m a l) T := by
    have hh : Tmix m a A=mpair (qmix m a l) T := Tmix_atom ..
    change T0 p n a A + Tmix m a A + α * role p n A=_
    rw [hh,add_right_comm]
    exact congrArg (·+_) (coreRole p w hw α hg h l s y)
  change innerP p x i A + (Tsym m a + α • role p n) A = dialed p l f y+_
  rw [show innerP p x i A=mpair M T from ht s z,h0, ←mpair_outer,mpair_add]
  change mpair M T+(dialed p l f y + _) = dialed p l f y+(mpair M T+_)
  rw [add_left_comm]; rfl
end HadwigerCounterexample

end

end OAI
