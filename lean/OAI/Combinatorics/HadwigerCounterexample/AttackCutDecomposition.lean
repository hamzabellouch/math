import OAI.Combinatorics.HadwigerCounterexample.ResponseAnnihilators

namespace OAI

/-! # Attack Cut Decomposition -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Submodule LinearMap Module Finset
open scoped BigOperators
variable {p : Shape} {n : ℕ}
variable {I J : Type} [Fintype I] [Fintype J]

theorem colSp_kill (S : Space (Vec I)) (M : Mat I J) :
    colSp M ≤ annih S ↔ ∀ x∈S,Mᵀ *ᵥ x=0 := by
  constructor
  · intro h x hx
    refine dot_ext_zero fun y => ?_
    rw [dotProduct_transpose_mulVec,dotProduct_comm]
    exact (annih_mem ..).mp (h ⟨y,rfl⟩) x hx
  rintro h z ⟨y,rfl⟩
  rw [annih_mem]; intro x hx
  rw [dotProduct_comm,mulVecLin_apply,←dotProduct_transpose_mulVec,h x hx,dotProduct_zero]

theorem box_kill {S : Space (Vec I)} {T : Space (Vec J)} {M : Mat I J} :
    M∈box (annih S) (annih T) ↔ (∀ x∈S,Mᵀ *ᵥ x=0) ∧ (∀ y ∈ T,M *ᵥ y=0) := by
  rw [box_mem,colSp_kill,colSp_kill,transpose_transpose]

theorem orth_sub {f b : Plan p n} {x y : Xpair p n} {C : ChanOut p n} {j}
    (hx : orth p C f b j x) (hy : orth p C f b j y) : orth p C f b j (x-y) := by
  intro D hd A ha; rw [map_sub,hx _ hd _ ha,hy _ hd _ ha,sub_self]

theorem orth_sum {f b : Plan p n} (x : I→Xpair p n) (c : I→F) {C : ChanOut p n} {j}
    (hx : ∀ i,orth p C f b j (x i)) : orth p C f b j (∑ i,c i • x i) := by
  intro D hd A ha
  rw [map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [map_smul,hx i _ hd _ ha,smul_zero]

namespace Volley
variable (v : Volley p n I)

def strike (t : Tagging p I) (ht : v.legal t) (j : I) : Xpair p n :=
  Pi.single (v.obj j) (⟨v.atomAt t j,atom_mem _ (ht j)⟩ : Xspace p n)

theorem strike_here (t : Tagging p I) (ht : v.legal t)
    (c : I → F) (i : Bool) :
    ((∑ j : I, c j • v.strike t ht j) i).val=∑ j∈v.here i,c j • v.atomAt t j := by
  classical
  rw [Finset.sum_apply]
  simp only [Submodule.coe_sum, Pi.smul_apply,Submodule.coe_smul,here,Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : v.obj j=i
  · simp only [ite_eq_left h]
    unfold strike
    rw [h,Pi.single_eq_same]
  simp [strike,h]

omit [Fintype I] in
theorem strike_pair (t : Tagging p I) (ht : v.legal t) (j : I) (e : Comp p.g) :
    purePair p n (v.strike t ht j) e=
    if inc e (t j) then vecMulVec (v.rayLoc j) (v.rayLoc j) else 0 := by
  classical
  simp only [purePair, Finset.sum_apply]
  rw [Finset.sum_eq_single (v.obj j)]
  · rw [strike,Pi.single_eq_same]
    change liftM _ _ (atom p _ _ _ e)=_
    rw [atom_def]; split
    · exact liftM_outer _ _ _ _
    rw [map_zero]
  · intro i _ hi; rw [strike,Pi.single_eq_of_ne hi]; exact map_zero _
  simp

theorem strike_orth {a b : Plan p n} {C : ChanOut p n} {i : Bool}
    (t : Tagging p I) (ht : v.legal t) (j : I) :
    orth p C (v.frozen a t) b i (v.strike t ht j) := by
  intro D hd A ha
  change ∑ e, _ = _
  refine Finset.sum_eq_zero fun e _ => ?_
  rw [v.strike_pair]
  by_cases h : inc e (t j)
  · have hy (z) : v.rayLoc j ∈ (v.frozen a t (e,z)) :=
      Submodule.mem_sup_right (colSp_mem (P:=v.keyM t e) (⟨j,h⟩ : visits p t e))
    let V := v.rayLoc j
    have h1 : A e *ᵥ V=0 := (box_kill.mp ((pureSpace_mem _).mp ha e)).2 V (hy false)
    have h2 (z) : D (e,z) *ᵥ V=0 :=
      (box_kill.mp ((deltaSpace_mem _).mp hd _)).2 V (hy z)
    rw [ite_eq_left h,mpair_outer,evmat]
    change dotProduct V (((C (e,true))ᵀ * D (e,false)+
      (D (e,true))ᵀ * C (e,false)+A e) *ᵥ V)=_
    simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec,h1,h2,mulVec_zero,
      dotProduct_zero,zero_add,add_zero,dotProduct_transpose_mulVec]
  rw [ite_eq_right h,map_zero]
end Volley

def labStruct (p : Shape) (n : ℕ) (M : Moment p n) (R : ℕ)
    (L : Finset (Label p.b)) (Z : Label p.b→BaseMat p n) :=
  M=labelSum p L Z ∧ L.card ≤ R ∧ (∀ s,s∉L → Z s=0) ∧
    ∀ s∈L,(Z s)ᵀ=Z s ∧ ∀ i,Z s i i=Z s none i

private theorem struct_tri {M1 M2 M3 : Moment p n} {R : ℕ}
    {L1 L2 L3 : Finset (Label p.b)} {Z1 Z2 Z3 : Label p.b→BaseMat p n}
    (h1 : labStruct p n M1 R L1 Z1)
    (h2 : labStruct p n M2 R L2 Z2)
    (h3 : labStruct p n M3 R L3 Z3)
    (hr : 3*R≤p.j) (hm : M1+M2+M3=0) (s : Label p.b) :
    Z1 s+Z2 s+Z3 s=0 := by
  classical
  let W := L1∪L2∪L3
  have hs1 : L1⊆W := subset_trans subset_union_left subset_union_left
  have hs2 : L2⊆W := subset_trans subset_union_right subset_union_left
  have hs3 : L3⊆W := subset_union_right
  have hh : W.card ≤ p.j+1 :=
    (Finset.card_union_le (L1∪L2) L3).trans ((add_le_add
      ((Finset.card_union_le L1 L2).trans (add_le_add h1.2.1 h2.2.1)) h3.2.1).trans (by omega))
  by_cases hs : s∈W
  · have hv {M : Moment p n} {L Z} (h : labStruct p n M R L Z) (hL : L ⊆ W)
        (i j : AIdx p.g n) (r : SelIdx p.b p.j) :
        (∑ s∈W,Z s i j*monoBit s r.val) = M (r,i) (emptySel,j) := by
      rw [h.1,labelSum, Matrix.sum_apply,←Finset.sum_subset hL]
      · simp only [mput_apply,emptySel,monoBit,Finset.prod_empty,mul_one,mul_comm]
      intro y _ hy
      simp [h.2.2.1 y hy]
    ext i j
    refine selector_indep W (fun s => (Z1 s i j+Z2 s i j+Z3 s i j)) p.j hh ?_ s hs
    intro T hT
    let r : SelIdx p.b p.j := ⟨T,hT⟩
    simp only [add_mul,Finset.sum_add_distrib]
    rw [hv h1 hs1 i j r,hv h2 hs2 i j r,hv h3 hs3 i j r]
    exact congr_fun (congr_fun hm (r,i)) (emptySel,j)
  rw [h1.2.2.1 s (fun h => hs (hs1 h)), h2.2.2.1 s (fun h => hs (hs2 h)),
    h3.2.2.1 s (fun h => hs (hs3 h)), zero_add,zero_add]

namespace Volley
variable {v : Volley p n I}

private theorem orth_structure {x : Xpair p n} {a b : Plan p n}
    {C : ChanOut p n} {t : Tagging p I} {w : I→Bool} {j : Bool}
    (hb : v.bounded w) (ho : orth p C (v.frozen a t) b j x)
    (R : ℕ) (hr : 2*planRank a+28≤R) (hj : 6*R+4 ≤ p.j)
    (i : Bool) (e : Comp p.g) :
    ∃ L Z,labStruct p n ((x i).val e) R L Z := by
  classical
  have h (z) := v.frozen_here_dim hb a t i z
  have he : ((x i).val e).rank ≤ R :=
    (rank_vanish (vanish_one ho i e)).trans
      ((Nat.add_le_add (h (e,true)) (h (e,false))).trans (by omega))
  have hf : ((x i).val e)∈ Wspace p n := by
    obtain ⟨w,h,hx⟩ := mem_X.mp (x i).property
    rw [← hx]
    exact ((Wspace p n).add_mem ((Wtag_le _) (h e.val.1)) ((Wtag_le _) (h e.val.2)))
  obtain ⟨L,Z,hL,_,hZ,hA⟩ := label_support hf R hj he
  let g (s : Label p.b) := if s∈L then Z s else 0
  refine ⟨L,g,?_,hL,(fun s hs => ite_eq_right hs), fun s hs => ?_⟩
  · rw [hZ]
    exact Finset.sum_congr rfl fun s hs => by simp [g,hs]
  simp only [g,ite_eq_left hs]
  exact hA _ hs

private theorem edge_at (l : Tag p.g) (e : Comp p.g) (h : inc e l) :
    ∃ (k : Tag p.g) (h : l≠k),e = edge l k h := by
  rcases e with ⟨⟨i,j⟩,hj⟩
  change i=l∨j=l at h
  rcases h with rfl|rfl
  · exact ⟨j,hj.ne,(edge_eq hj).symm⟩
  exact ⟨i,hj.ne.symm, by rw [edge_symm,edge_eq hj]⟩

private theorem cut_tri {x : Profile p n} (hx : x∈Xspace p n)
    (l k j : Tag p.g) (h : l≠k) (h' : l ≠ j) (h'' : k≠j) :
    x (edge l k h)+x (edge l j h')+x (edge k j h'')=0 := by
  obtain ⟨w,hv,rfl⟩ := mem_X.mp hx
  rw [← getPair_edge l k h (cut p n w), ←getPair_edge l j h' (cut p n w), ←getPair_edge k j h'' (cut p n w),
    getPair_cut,getPair_cut,getPair_cut]
  have he (x y z : Moment p n) : x+y+(x+z)+(y+z)=0 := calc
    _ = (x+x)+(y+y)+(z+z) := by ac_rfl
    _ = _ := by simp only [char_two]
  exact he _ _ _

private theorem structure_mark {x : Xpair p n} {a b : Plan p n}
    {C : ChanOut p n} {t : Tagging p I} {w : I→Bool} {j : Bool}
    {q R : ℕ} (hb : v.bounded w) (ho : orth p C (v.frozen a t) b j x) (hv : v.avoids a q)
    (hr : 6*R+4≤p.j) (hq : R+14≤q)
    (l : I)
    {L : Comp p.g → Finset (Label p.b)} {Z : Comp p.g → Label p.b → BaseMat p n}
    (he : ∀ e,labStruct p n ((x (v.obj l)).val e) R (L e) (Z e)) :
    ∃ c : F, ∀ e,mput p (v.sel l) (Z e (v.sel l))=c • v.atomAt t l e := by
  classical
  let s := v.sel l
  let u := t l
  let M := vecMulVec (baseV (v.par l)) (baseV (v.par l))
  let coeff := fun e : Comp p.g => Z e s none none
  have h1 (e : Comp p.g) : Z e s= if inc e u then coeff e • M else 0 := by
    have ⟨hE,hL,hT,hH⟩ := he e
    exact mark_atom hb t hv l e _ (le_trans (Nat.add_le_add_right hL 14) hq)
      _ hT hH (hE ▸ vanish_one ho (v.obj l) e)
  have h2 (e f : Comp p.g) (h : inc e u) (h' : inc f u) :
      coeff e=coeff f := by
    by_cases hi : e=f
    · rw [hi]
    obtain ⟨k,hk,rfl⟩ := edge_at u e h
    obtain ⟨u2,hl,rfl⟩ := edge_at u f h'
    have hj : k ≠ u2 := by rintro rfl; exact hi rfl
    have hh := cut_tri (x (v.obj l)).property u k u2 hk hl hj
    have heq := struct_tri (he (edge u k hk)) (he (edge u u2 hl)) (he (edge k u2 hj))
      (by omega) hh s
    have hn : ¬ inc (edge k u2 hj) u := fun he => by
      rcases (inc_edge_iff _).mp he with h|h; exact hk h.symm; exact hl h.symm
    rw [h1 (edge k u2 hj), ite_eq_right hn,add_zero] at heq
    have h0 := congr_fun (congr_fun heq none) none
    change coeff _ + coeff _ = 0 at h0
    exact add_right_cancel (h0.trans (char_two _).symm)
  have h3 (e) : mput p s (Z e s)= coeff e • v.atomAt t l e := by
    rw [h1,atomAt,atom_def]
    by_cases hf : inc e u
    · rw [ite_eq_left hf,ite_eq_left hf,map_smul]
      change coeff e • liftM (labMat p n s) (labMat p n s) M=_
      unfold M
      rw [liftM_outer,labMat_act]; rfl
    rw [ite_eq_right hf,ite_eq_right hf,map_zero,smul_zero]
  by_cases hh : ∃ e,inc e u
  · obtain ⟨f,hf⟩ := hh
    refine ⟨coeff f,fun e => ?_⟩
    by_cases h : inc e u
    · exact (h3 e).trans (by rw [h2 e f h hf])
    refine (h3 e).trans ?_
    rw [atomAt,atom_def,ite_eq_right h,smul_zero,smul_zero]
  refine ⟨0,fun e => ?_⟩
  refine (h3 e).trans ?_
  rw [atomAt,atom_def,ite_eq_right (show ¬inc e u from fun he => hh ⟨e,he⟩),
    smul_zero,zero_smul]

/-- a component uses at most R nonattack labels. -/
def clean (v : Volley p n I) (i : Bool) (R : ℕ) (M : Moment p n) :=
  ∃ (L : Finset (Label p.b)) (Z : Label p.b → BaseMat p n),
    M=labelSum p L Z ∧ L.card≤R ∧ Disjoint L (v.marked i)

theorem split_orth {x : Xpair p n} {a b : Plan p n}
    {C : ChanOut p n} {t : Tagging p I} {w : I→Bool} {j : Bool}
    {q R : ℕ} (hb : v.bounded w) (ht : v.legal t)
    (ho : orth p C (v.frozen a t) b j x) (hv : v.avoids a q)
    (hr : 6*R+4≤p.j) (hr' : 2*planRank a+28≤R) (hq : R+14≤q) :
    ∃ (c : I → F) (y : Xpair p n), x=y+∑ i,c i • v.strike t ht i ∧
      orth p C (v.frozen a t) b j y ∧ ∀ i e,v.clean i R ((y i).val e) := by
  classical
  choose L Z hZ using orth_structure hb ho R hr' hr
  choose c hc using fun l => structure_mark hb ho hv hr hq l (hZ (v.obj l))
  let A := ∑ i,c i • v.strike t ht i
  refine ⟨c,x-A,(sub_add_cancel x A).symm,orth_sub ho (orth_sum _ _ (v.strike_orth t ht)),
    fun i e => ?_⟩
  obtain ⟨B,h1,hA,hv',h3⟩ := hv i
  let T := v.marked i
  have he : (A i).val e=labelSum p T (Z i e) := by
    rw [show (A i).val=_ from v.strike_here t ht c i, Finset.sum_apply]
    dsimp only [labelSum,T,marked]
    rw [Finset.sum_image h3]
    refine Finset.sum_congr rfl fun l hl => ?_
    have he : v.obj l=i := (mem_filter.mp hl).2
    exact (he ▸ hc l e).symm
  let W := L i e
  refine ⟨W \ T,Z i e,?_,(Finset.card_le_card sdiff_subset).trans (hZ i e).2.1, ?_⟩
  · change (x i).val e-(A i).val e=_
    rw [(hZ i e).1,he]
    have hz : labelSum p W (Z i e)=labelSum p (W∪T) (Z i e) := by
      refine Finset.sum_subset subset_union_left fun s _ hs => ?_
      rw [(hZ i e).2.2.1 s hs,map_zero]
    rw [hz]
    have hS : (W∪T)=(W \ T) ∪ T := by ext i; simp
    rw [hS,labelSum,Finset.sum_union (show Disjoint (W \ T) T from Disjoint.symm disjoint_sdiff)]
    exact add_sub_cancel_right _ _
  exact Disjoint.symm disjoint_sdiff

end Volley
end HadwigerCounterexample

end

end OAI
