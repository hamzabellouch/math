import OAI.Combinatorics.HadwigerCounterexample.RankEfficientDecomposition

namespace OAI

/-! # Primal Space Compression -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Finset
open scoped BigOperators
variable {p : Shape} {n : ℕ} {I J : Type} [Fintype I] [Fintype J]

private theorem exists_cover (S : J→Space (Vec I)) (D : ℕ) (h : ∀ j,dim (S j)≤D) :
    ∃ A : Space (Vec I),(∀ j,S j ≤ A) ∧ dim A≤Fintype.card J*D := by
  classical
  have hh (s : Finset J) :
      ∃ A : Space (Vec I),(∀ j∈s,S j≤A) ∧ dim A≤s.card*D := by
    induction s using Finset.induction with
    | empty => exact ⟨⊥,by simp, by simp [dim]⟩
    | insert a s ha ih =>
      obtain ⟨A,hA,hD⟩ := ih
      refine ⟨S a⊔A,fun j hj => ?_,?_⟩
      · rcases Finset.mem_insert.mp hj with rfl|g
        · exact le_sup_left
        exact (hA _ g).trans le_sup_right
      simpa only [Finset.card_insert_of_notMem ha,Nat.add_mul,one_mul,add_comm D] using
        ((Submodule.finrank_add_le_finrank_add_finrank (S a) A).trans (add_le_add (h a) hD))
  simpa only [Finset.mem_univ,true_imp_iff,card_univ] using hh Finset.univ

theorem compact_endo (S T : Space (Vec I)) :
    ∃ A : Mat I I,(∀ x∈S,A *ᵥ x=x) ∧ (∀ x∈T,Aᵀ *ᵥ x=x) ∧ A.rank≤dim S+dim T := by
  classical
  obtain ⟨A,hA⟩ := proj_exists S ⊥ disjoint_bot_right
  obtain ⟨B,hB⟩ := proj_exists T ⊥ disjoint_bot_right
  refine ⟨A+Bᵀ * (1-A),fun x hx => ?_,fun x hx => ?_,?_⟩
  · rw [Matrix.add_mulVec,←Matrix.mulVec_mulVec,Matrix.sub_mulVec,hA.fixes x hx,
      Matrix.one_mulVec,sub_self,Matrix.mulVec_zero,add_zero]
  · rw [Matrix.transpose_add,Matrix.add_mulVec,Matrix.transpose_mul,Matrix.transpose_transpose,
      ← mulVec_mulVec,hB.fixes x hx,Matrix.transpose_sub,Matrix.sub_mulVec,Matrix.transpose_one,
      Matrix.one_mulVec,add_sub_cancel]
  exact (mrk_add_le ..).trans (add_le_add (rank_maps S hA.onto) ((Matrix.rank_mul_le_left ..).trans
    (by rw [Matrix.rank_transpose]; exact rank_maps T hB.onto)))

abbrev Sel (p : Shape) := SelIdx p.b p.j
abbrev Nendo (p : Shape) (n : ℕ) := Block p.g→ Mat (Fin n) (Fin n)
def iFix (p : Shape) (n : ℕ) : Mat (Row p n) (Sel p) := embedMat (fun s => (s,none))
def iCoeff (p : Shape) (n : ℕ) (s : Sel p) (d : Block p.g) :
    Mat (Row p n) (Fin n) := embedMat (fun i => (s,some (d,i)))

/-- induced row vector transform. -/
def rowShrink (p : Shape) {n} (A : Nendo p n) : Mat (Row p n) (Row p n) :=
  iFix p n*(iFix p n)ᵀ +
  ∑ i : Sel p,∑ d : Block p.g,iCoeff p n i d*A d*(iCoeff p n i d)ᵀ

def readCoeff (p : Shape) {n} (s : Sel p) (d : Block p.g) (v : Ray p n) :=
  fun i => v (s,some (d,i))

theorem readCoeff_val (s : Sel p) (d : Block p.g) (v : Ray p n) :
    (iCoeff p n s d)ᵀ *ᵥ v=readCoeff p s d v := embedMatT _ _

theorem shrink_transpose (A : Nendo p n) :
    (rowShrink p A)ᵀ=rowShrink p (fun i => (A i)ᵀ) := by
  simp only [rowShrink,Matrix.transpose_add,Matrix.transpose_mul,
    Matrix.transpose_sum,Matrix.transpose_transpose,Matrix.mul_assoc]

private theorem coeff_none (A : Nendo p n) (v : Ray p n) (s : Sel p) :
    (rowShrink p A *ᵥ v) (s,none)=v (s,none) := by
  classical
  simp only [rowShrink,Matrix.add_mulVec, Matrix.sum_mulVec,←Matrix.mulVec_mulVec,readCoeff_val]
  unfold iFix iCoeff
  rw [embedMatT]
  simp [embedMat,Matrix.mulVec,dotProduct,Finset.sum_apply,Matrix.mul_apply]

set_option maxHeartbeats 600000 in
private theorem coeff_some (A : Nendo p n) (v : Ray p n) (s : Sel p)
    (d : Block p.g) (i : Fin n) :
    (rowShrink p A *ᵥ v) (s,some (d,i))=(A d *ᵥ (readCoeff p s d v)) i := by
  classical
  simp only [rowShrink,Matrix.add_mulVec, Matrix.sum_mulVec,←Matrix.mulVec_mulVec,readCoeff_val]
  simp only [Pi.add_apply,Finset.sum_apply]
  have hz (x) : (iFix p n *ᵥ x) (s,some (d,i))=0 := by
    simp [iFix,embedMat,Matrix.mulVec,dotProduct]
  rw [hz,zero_add]
  have hh (t : Sel p) (a : Block p.g) (x : Vec (Fin n)) :
      (iCoeff p n t a *ᵥ x) (s,some (d,i)) =
      if s=t then (if d=a then x i else 0) else 0 := by
    by_cases e : s=t <;> by_cases g : d=a <;> simp [iCoeff,embedMat,Matrix.mulVec,dotProduct,e,g]
  simp_rw [hh]
  rw [Finset.sum_eq_single s]
  · simp only [ite_true,Finset.sum_ite_eq,mem_univ]
  · intro a _ ha; simp only [ite_eq_right (Ne.symm ha),Finset.sum_const_zero]
  simp

private theorem coeff_fixes (A : Nendo p n) (v : Ray p n)
    (h : ∀ d s, A d *ᵥ (readCoeff p s d v) = readCoeff p s d v) :
    rowShrink p A *ᵥ v=v := by
  funext i
  rcases i with ⟨s, _|⟨d,i⟩⟩
  · rw [coeff_none]
  rw [coeff_some,h]
  rfl

def nbBlock (p : Shape) := Fintype.card (Block p.g)
def ncComp (p : Shape) := Fintype.card (Comp p.g)

theorem shrink_rank (A : Nendo p n) (D : ℕ) (h : ∀ i,(A i).rank ≤ D) :
    (rowShrink p A).rank≤ psize p+ psize p* (nbBlock p*D) := by
  apply le_trans (mrk_add_le ..)
  apply add_le_add
  · exact (Matrix.rank_mul_le_left ..).trans (iFix p n).rank_le_card_width
  refine (mrk_sum_le ..).trans ((Finset.sum_le_sum (g:=fun _ => nbBlock p*D) (fun i _ => ?_)).trans_eq
    (by simp [psize,Sel]))
  refine (mrk_sum_le ..).trans ((Finset.sum_le_sum (g:=fun _ => D) (fun i _ => ?_)).trans_eq
    (by simp [nbBlock]))
  exact ((Matrix.rank_mul_le_left ..).trans (Matrix.rank_mul_le_right ..)).trans (h i)

def dbits (p : Shape) (T R : ℕ) := ncComp p*2* psize p*(T+R)
def drow (p : Shape) (T R : ℕ) := psize p+psize p*(nbBlock p*dbits p T R)

theorem shrink_both (S T : Place p → Space (Ray p n)) (K R : ℕ)
    (hk : ∀ z,dim (S z) ≤K) (hr : ∀ z,dim (T z)≤R) :
    ∃ A : Nendo p n,
      (∀ z,∀ x∈S z,rowShrink p A *ᵥ x=x) ∧
      (∀ z,∀ x∈T z,(rowShrink p A)ᵀ *ᵥ x=x) ∧
      (rowShrink p A).rank ≤ drow p K R := by
  classical
  let W := Place p×Sel p
  have hp : Fintype.card (Place p×Sel p)=ncComp p*2*psize p := by
    simp only [Place,Fintype.card_prod,ncComp,Fintype.card_bool,psize,Sel]
  let G d (S : Place p → Space (Ray p n)) (z : Place p×Sel p) :=
    (S z.1).map (iCoeff p n z.2 d)ᵀ.mulVecLin
  obtain ⟨A,hA,hT,hL⟩ :
      ∃ A : Nendo p n,
        (∀ d z,∀ x∈G d S z,A d *ᵥ x=x) ∧
        (∀ d z,∀ x∈G d T z,(A d)ᵀ *ᵥ x=x) ∧ ∀ i,(A i).rank≤dbits p K R := by
    have he (d : Block p.g) :
        ∃ A : Mat (Fin n) (Fin n), (∀ z,∀ x∈G d S z,A *ᵥ x=x) ∧
        (∀ z,∀ x∈G d T z,Aᵀ *ᵥ x=x) ∧ A.rank≤dbits p K R := by
      obtain ⟨X,hX,hD⟩ := exists_cover (G d S) K (fun j => (Submodule.finrank_map_le ..).trans
        (hk j.1))
      obtain ⟨Y,hY,hD'⟩ := exists_cover (G d T) R (fun j => (Submodule.finrank_map_le ..).trans
        (hr j.1))
      obtain ⟨A,hA,hZ,hL⟩ := compact_endo X Y
      refine ⟨A,(fun z x hx => hA x (hX z hx)),(fun z x hx => hZ x (hY z hx)),?_⟩
      rw [hp] at hD hD'
      exact hL.trans ((add_le_add hD hD').trans_eq (Nat.mul_add ..).symm)
    choose A hA hZ hL using he
    exact ⟨A,hA,hZ,hL⟩
  have he (X : Place p → Space (Ray p n)) (z)
      (x : Ray p n) (hx : x∈X z) (d s) : readCoeff p s d x∈ G d X (z,s) :=
    ⟨x,hx,readCoeff_val ..⟩
  refine ⟨A,fun z x hx => ?_,fun z x hx => ?_,shrink_rank A _ hL⟩
  · exact coeff_fixes A x (fun d s => hA _ (z,s) _ (he S z x hx d s))
  rw [shrink_transpose]
  exact coeff_fixes _ _ (fun d s => hT _ (z,s) _ (he T z x hx d s))

private def shrinkBase (A : Nendo p n) (v : Base p.g n) : Base p.g n :=
  fun x => (A x.1 *ᵥ (fun j => v (x.1,j))) x.2

private theorem shrink_point (A : Nendo p n) (s : Label p.b) (z : Base p.g n) :
    rowShrink p A *ᵥ point p s z=point p s (shrinkBase (p:=p) A z) := by
  classical
  funext i
  rcases i with ⟨r,_|⟨d,i⟩⟩
  · rw [coeff_none]; rfl
  rw [coeff_some]
  simp only [point_eval,readCoeff,shrinkBase,Matrix.mulVec,dotProduct,
    baseV,Option.elim',Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => mul_left_comm ..

private theorem shrink_tag (A : Nendo p n) (l : Tag p.g) (M : Moment p n) (h : M∈Wtag p n l) :
    liftM (rowShrink p A) (rowShrink p A) M∈Wtag p n l := by
  classical
  unfold Wtag at h
  induction h using Submodule.span_induction with
  | mem m hm =>
    obtain ⟨s,z,hz,rfl⟩ := hm
    simp only [mom,liftM_outer,shrink_point]
    apply Submodule.subset_span
    refine ⟨s,shrinkBase (p:=p) A z,?_,rfl⟩
    intro d t hd i
    change (A (Block.O d t) *ᵥ _) i = _
    simp only [Matrix.mulVec,dotProduct,hz _ _ hd,mul_zero,Finset.sum_const_zero]
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y hx hy ih ih' => rw [map_add]; exact Submodule.add_mem _ ih ih'
  | smul a x hx ih => rw [map_smul]; exact Submodule.smul_mem _ _ ih

theorem shrink_X (A : Nendo p n) (M : Profile p n) (h : M∈Xspace p n) :
    (fun e : Comp p.g => liftM (rowShrink p A) (rowShrink p A) (M e))∈Xspace p n := by
  obtain ⟨w,hw,rfl⟩ := mem_X.mp h
  refine mem_X.mpr ⟨_,(fun l => shrink_tag A l _ (hw l)),?_⟩
  funext i
  exact (map_add (liftM (rowShrink p A) (rowShrink p A)) _ _).symm

end HadwigerCounterexample

end

end OAI
