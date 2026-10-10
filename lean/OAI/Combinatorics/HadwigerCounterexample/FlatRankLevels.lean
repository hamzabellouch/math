import OAI.Combinatorics.HadwigerCounterexample.BooleanLabels
import OAI.Combinatorics.HadwigerCounterexample.FlatLevelShifts

namespace OAI

/-! # Flat Rank Levels -/

noncomputable section
namespace HadwigerCounterexample
open Matrix
open scoped BigOperators
variable {p : Shape} {n k : ℕ}

abbrev Layer (p : Shape) (n k : ℕ) := SelIdx p.b k × AIdx p.g n

def rise (p : Shape) {n k m} (h : k≤m) (i : Layer p n k) : Layer p n m :=
  (⟨i.1.val,i.1.property.trans h⟩,i.2)

def bump (p : Shape) {n k} (a : Fin p.b) (i : Layer p n k) : Layer p n (k+1) :=
  (⟨insert a i.1.val,(Finset.card_insert_le ..).trans (Nat.add_le_add_right i.1.property 1)⟩,i.2)

def atLayer (M : Moment p n) {k : ℕ} (h : k≤p.j) := M.submatrix (rise p h) (rise p h)

theorem rank_atLayer_le (M : Moment p n) {k : ℕ} (h : k≤p.j) :
    (atLayer M h).rank ≤ M.rank := M.rank_submatrix_le _ _

private theorem atLayer_mono (M : Moment p n) {k l} (h : k≤l) (hh : l≤p.j) :
    (atLayer M (h.trans hh)).rank ≤ (atLayer M hh).rank := by
  let f := (rise p (n:=n) h)
  have he := (atLayer M hh).rank_submatrix_le f f
  exact he

theorem flat_atLayer (M : Moment p n) {R : ℕ} (hR : M.rank ≤ R)
    (hj : 6*R+4 ≤ p.j) :
    ∃ (k : ℕ) (h : k+1≤p.j), 4*R+2≤k ∧
      (atLayer M ((Nat.le_succ k).trans h)).rank = (atLayer M h).rank := by
  classical
  by_contra hn
  let a := 4*R+2
  have hi (i : ℕ) (h : a+i ≤ p.j) :
      i ≤ (atLayer M h).rank := by
    induction i with
    | zero => exact Nat.zero_le _
    | succ i ih =>
      have he : a+i ≤ p.j := (Nat.le_succ _).trans h
      have hh : (atLayer M he).rank < (atLayer M h).rank := by
        refine lt_of_le_of_ne (atLayer_mono M (Nat.le_succ _) h) (fun hx => hn ?_)
        exact ⟨a+i,h,by unfold a; omega,hx⟩
      exact (Nat.succ_le_succ (ih he)).trans hh
  have he : a+(R+1)≤p.j := by unfold a; omega
  have hx := ((hi (R+1) he).trans (rank_atLayer_le M he)).trans hR
  omega

theorem flat_entries {M : Moment p n} (hs : Mᵀ=M) (hh : hankel M)
    (hk : k+1≤p.j) (hr :
      (atLayer M ((Nat.le_succ _).trans hk)).rank = (atLayer M hk).rank) :
    let t := (atLayer M hk).rank
    ∃ (s : Fin t → Label p.b) (u v : Fin t → Vec (AIdx p.g n)),
      ∀ i j : Layer p n k,
        atLayer M ((Nat.le_succ _).trans hk) i j = ∑ x : Fin t,
          monoBit (s x) i.1.val * monoBit (s x) j.1.val * (u x i.2 * v x j.2) := by
  classical
  intro t
  let h := (Nat.le_succ k).trans hk
  let A := atLayer M hk
  let r := rise p (n:=n) (Nat.le_succ k)
  obtain ⟨Q,H,hQ,_,hH,hA⟩ := rank_symmetric A (show Aᵀ=A by
    ext i j
    exact congr_fun (congr_fun hs _) _)
  let P := Q.submatrix r id
  let X := fun i => Q.submatrix (bump p (k:=k) i) id
  have eqn (a b : Layer p n k → Layer p n (k+1)) :
      Q.submatrix a id * H * (Q.submatrix b id)ᵀ = A.submatrix a b := by

    have he :
        Q.submatrix a id * H * (Q.submatrix b id)ᵀ =
          (Q*H*Qᵀ).submatrix a b := by ext; rfl
    exact he.trans (congrArg (fun m => m.submatrix a b) hA)
  have hL : P*H*Pᵀ=atLayer M h := eqn _ _
  have hP : Function.Injective P.mulVec := by
    rw [mrk_inj,Fintype.card_fin]
    apply le_antisymm (by simpa using P.rank_le_card_width) ?_
    have hh := (Matrix.rank_mul_le_left (P*H) Pᵀ).trans (Matrix.rank_mul_le_left P H)
    rw [hL] at hh
    rwa [hr] at hh
  have hentry (x y a b : Layer p n (k+1))
      (h1 : x.2 = a.2) (h2 : y.2=b.2)
      (h3 : x.1.val∪y.1.val=a.1.val∪b.1.val) : A x y=A a b := by
    change M (⟨_,_⟩,x.2) (⟨_,_⟩,y.2) = M (⟨_,_⟩,a.2) (⟨_,_⟩,b.2)
    rw [h1,h2]; exact hh _ _ _ _ _ _ h3
  obtain ⟨K,C,f,hf,hd⟩ := shift_factors P H hP hH X
    (fun a => by
      unfold X P; rw [eqn,eqn]; ext i j
      apply hentry <;> simp [bump,r,rise])
    (fun a b => by
      unfold X; rw [eqn,eqn]; ext i j
      apply hentry <;> try rfl
      simp only [bump]
      ext; simp; tauto)
    (fun a => by
      unfold X P; rw [eqn,eqn]; ext i j
      apply hentry <;> try rfl
      simp only [bump,r,rise]
      ext; simp)
  let s (x : Fin t) : Label p.b := fun a => f a x
  have hi (F : Mat (Fin t) (Fin t)) (hF : ∀ a, X a * F=P*F*diagonal (f a))
      (x : Fin t) (i : Layer p n k) :
      (P*F) i x = monoBit (s x) i.1.val * (P*F) (emptySel,i.2) x := by
    rcases i with ⟨⟨l,hl⟩,i⟩
    induction l using Finset.induction with
    | empty =>
      simp only [monoBit,Finset.prod_empty,one_mul]
      rfl
    | insert a l ha ih =>
      have hg := Finset.card_insert_of_notMem ha
      have he : l.card≤k := by omega
      let u : Layer p n k := (⟨l,he⟩,i)
      have hh := congr_fun (congr_fun (hF a) u) x
      rw [Matrix.mul_diagonal] at hh
      change (P*F) (⟨insert a l,hl⟩,i) x = _
      change (P*F) (⟨insert a l,hl⟩,i) x = (P*F) u x * _ at hh
      rw [hh]
      change (P*F) (⟨l,he⟩,i) x * s x a = monoBit (s x) (insert a l) * _
      rw [ih he,mono_insert]
      ring
  let u := P*K
  let v := P*C
  refine ⟨s,fun x i => u (emptySel,i) x, fun x i => v (emptySel,i) x,fun i j => ?_⟩
  have he : u*vᵀ=atLayer M h := by rw [← hL,hf]; simp only [u,v,Matrix.transpose_mul,
    Matrix.mul_assoc]
  rw [← he]
  simp only [Matrix.mul_apply,Matrix.transpose_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hu := hi K (fun a => (hd a).2) x i
  have hv := hi C (fun a => (hd a).1) x j
  dsimp only [u,v] at *
  rw [hu,hv]
  ring

end HadwigerCounterexample

end

end OAI
