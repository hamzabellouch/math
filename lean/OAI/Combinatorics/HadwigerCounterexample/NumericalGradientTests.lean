import OAI.Combinatorics.HadwigerCounterexample.StatusRecipes

namespace OAI

/-! # Numerical Gradient Tests -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Module LinearMap Function Submodule
open scoped BigOperators
namespace StatusAnalysis
variable {p : Shape} {n N : ℕ} {q : Format} {d e : Rates}
def mailRole {b} (a : Amounts p q d b) :=
  fun i=>(a i).2.1.1
def mailBias {b} (a : Amounts p q d b) :=
  fun i=>(a i).2.2

theorem aim_sum {H : Type} [AddCommMonoid H] (b : Bool) (x : Grid) (u : Messenger q→H) :
    ∑ j∈aiming (parcel b) (parcel (!b)) (sendId b x) (sendId (!b) x),u j=∑ i:Fin (q x),u ⟨x,i⟩ := by
  let p : Shape := ⟨0,0,0,0,0,0⟩
  let v : Volley p 0 (Messenger q) := ⟨parcel b,fun _ =>0,fun _=>0⟩
  exact sum_shots b v x rfl _
def TMill (p : Shape) {b} {d} (t : Tagging p (Messenger q)) (w : Amounts p q d b) :
    Mat (Messenger q) (Messenger q) :=
  let a (x : Tag p.g) (i : Messenger q) := ∑ z:Tag p.g,(w i).1 (Sum.inl (z,x))
  let f (x : Tag p.g) (i : Messenger q) :=
    let c:=(w i).1 (Sum.inr ())
    c+(if t i=x then c else 0)
  Matrix.of fun i j => mailRole w i * mailRole w j +
    ∑ x:Tag p.g,(a x i * f x j + f x i * a x j)
theorem tmill_sym {b} (t : Tagging p (Messenger q)) (w : Amounts p q d b) :
    (TMill p t w)ᵀ=TMill p t w := by
  classical
  ext i j
  unfold TMill; simp only [transpose_apply,Matrix.of_apply]; congr 1
  · ring
  exact Finset.sum_congr rfl fun _ _ => by ring

def proclaims {b : Bool} (p : Shape) {d e}
    (a : Amounts p q d b) (w : Amounts p q e (!b)) (t : Tagging p (Messenger q))
    (g : Script p (Messenger q)) :=
  fulfills p t (mailRole a) (mailBias w) (TMill p t a) g (parcel b) (parcel (!b))

theorem funds_roles {b} (a : Amounts p q d b) (i : Grid) :
    (funds a i).1.1=∑ x : Fin (q i), mailRole a ⟨i,x⟩ := by
  let entries : Fin (q i) → Whole (d (sendId b i)) := fun k => (a ⟨i,k⟩).2
  change (∑ k, entries k).1.1 = _
  rw [Prod.fst_sum,Prod.fst_sum]
  rfl
theorem funds_duos {b} (a : Amounts p q d b) (i : Grid) :
    couple _ (funds a i)=
      ∑ x: Fin (q i), (mailRole a ⟨i,x⟩+mailBias a ⟨i,x⟩) := by
  let entries : Fin (q i) → Whole (d (sendId b i)) := fun k => (a ⟨i,k⟩).2
  change couple _ (∑ k, entries k) = _
  rw [map_sum]
  rfl

set_option maxHeartbeats 800000 in
theorem proclaim_script (b : Bool) (a : Amounts p q d b) (w : Amounts p q e (!b)) (t : Tagging p
    (Messenger q))
    (v : Charts p n e) (M : Cross p n)
    (h : rhyme a w) (hb : ∀ i,1≤ q i)
    (hr : still (!b) w v M)
    (hg : 2≤p.g) (hj : 1≤p.J) : ∃ s, proclaims p a w t s := by
  have ha {H : Type} [AddCommMonoid H] (a e : Nodes) (f : Messenger q→ H) :
      ∑ x∈aiming (parcel b) (parcel (!b)) a e, f x=∑ i:Fin (q (transit b (a,e))),f
        ⟨transit b (a,e),i⟩ := by
    have hA := aim_sum b (transit b (a,e)) f
    have he := (sendPair b (transit b (a,e))).trans (transit_inv b _)
    rw [show sendId b _ = a from congrArg Prod.fst he,
      show sendId (!b) _=e from congrArg Prod.snd he] at hA
    exact hA
  apply choose_script p t _ _ _ _ (mailRole w) _ _ _ _ (tmill_sym ..) hg hj
  · intro i
    rw [ha,ha,←funds_duos w,←funds_duos w]
    have hx:=hr.2 i; cases b <;> exact hx
  · intro i j; rw [ha,sum_add_distrib,←funds_roles a, ←funds_roles w]
    exact h _
  intro i j
  let k:=transit b (i,j)
  let x : Messenger q:=⟨k,0,(hb k)⟩
  have he := (sendPair b k).trans (transit_inv b (i,j))
  exact ⟨x,Finset.mem_filter.mpr ⟨mem_univ _,congrArg Prod.fst he,congrArg Prod.snd he⟩⟩

theorem tmill_formula {b} (t : Tagging p (Messenger q)) (hg : Odd p.g) (v : Charts p n d)
    (l f) (x : Inputs p n (Messenger q)) (m : Mixer p n) (o : UnitType p n N)
    (a : Amounts p q d b) (h : printed b v t l f m o x=a) (i j : Messenger q) :
    T0 p n (useAtom p (t i) (l i) (f i) (x i)) (useAtom p (t j) (l j) (f j) (x j)) =
      TMill p t a i j := by
  classical
  rw [← h]
  simp_rw [T0_val, roleT_scan,sharedT_scan _ hg]
  rfl

theorem procl_grad (t : Tagging p (Messenger q))
    {b} (a : Amounts p q d b) (w : Amounts p q e (!b))
    (hg : Odd p.g) (v : Charts p n d) (v' : Charts p n e)
    (l f l' f') (x y : Inputs p n (Messenger q))
    (m : Mixer p n) (o z : UnitType p n N)
    (h : printed b v t l f m o x=a) (hz : printed (!b) v' t l' f' m z y=w)
    (s : Script p (Messenger q)) (hs : proclaims p a w t s) :
    let u:=(manager b t l f).draw x
    u.reads s m → u.attackGrad ((manager (!b) t l' f').draw y) t m z := by
  intro u hu
  apply Volley.grads_by_script (v:=u) t m ((manager (!b) t l' f').draw y) z (d:=mailRole a) (f:=mailBias w) (u:=TMill p t a) (s:=s) hs hu
  · rw [← h]; intro; rfl
  · rw [←hz]; intro; rfl
  exact tmill_formula t hg v l f x m o a h

set_option maxHeartbeats 600000 in
theorem rhyme_match (t : Tagging p (Messenger q)) (a : Amounts p q d true)
    (w : Amounts p q e false)
    (v : Charts p n d) (v' : Charts p n e)
    (l f l' f') (x y : Inputs p n (Messenger q))
    (m : Mixer p n) (o z : UnitType p n N)
    (h : printed true v t l f m o x=a) (hz : printed false v' t l' f' m z y=w)
    (he : rhyme a w) :
    let u:=(manager true t l f).draw x
    u.roleMatch ((manager false t l' f').draw y) t := by
  classical
  intro u i j
  let q:= (i,j)
  let s:= (manager false t l' f').draw y
  have hh : u.sumAt t s.obj i j=unionAt (u.atomAt t) (i,j) :=
    sumAtSend true u t (i,j) rfl
  have hf : s.sumAt t u.obj j i=unionAt (s.atomAt t) (i,j) := sumAtSend false s t (i,j) rfl
  change _ + role _ _ (s.sumAt _ _ _ _)=_
  rw [hh,hf]
  specialize he (i,j)
  change (funds a (i,j)).1.1+(funds w (i,j)).1.1=1 at he
  rw [funds_reg t true v m o l f x a h,funds_reg t false v' m z l' f' y w hz] at he
  exact he
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
