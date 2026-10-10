import OAI.Combinatorics.HadwigerCounterexample.FlatRankLevels

namespace OAI

/-! # Moment Label Support -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Finset
open scoped BigOperators
variable {p : Shape} {n k : ℕ}

/-- Zero extension by the Boolean union rule for low rank matrices. -/
theorem zero_extension {M : Moment p n} (hh : hankel M) (hr : M.rank≤k)
    (hk : k≤p.j) (hg : atLayer M hk=0) : M=0 := by
  classical
  by_contra he
  let D (r : ℕ) := ∃ i j : Row p n,M i j≠0 ∧ (i.1.val∪j.1.val).card=r
  have hD : ∃ r,D r := by
    by_contra! h
    refine he (Matrix.ext fun i j => ?_)
    exact Classical.byContradiction fun g => h _ ⟨i,j,g,rfl⟩
  obtain ⟨x,y,hxy,hw⟩ := Nat.find_spec hD
  let U := x.1.val∪y.1.val
  let d := U.card
  have hd : k<d := by
    by_contra hd
    have hx : x.1.val.card≤k := (Finset.card_le_card subset_union_left).trans (Nat.le_of_not_gt hd)
    have hy : y.1.val.card≤k := (Finset.card_le_card subset_union_right).trans (Nat.le_of_not_gt hd)
    exact hxy (congr_fun (congr_fun hg (⟨x.1.val,hx⟩,x.2)) (⟨y.1.val,hy⟩,y.2))
  have hd' : d≤2*p.j := by
    have hi := x.1.property; have hj := y.1.property
    exact (card_union_le _ _).trans (by omega)
  let t := d/2
  let T := U.powersetCard t
  have hi (i : T) := mem_powersetCard.mp i.property
  have hs (i : T) : (U\i.val).card ≤ p.j := by
    rw [Finset.card_sdiff_of_subset (hi i).1,(hi i).2]
    change d - (d/2) ≤ _
    omega
  let f : T → Row p n := fun i => (⟨i.val, (hi i).2 ▸ (show t≤p.j by
    unfold t; omega)⟩, x.2)
  let g : T → Row p n := fun i => (⟨U\i.val, hs i⟩,y.2)
  have hf : M.submatrix f g=1 := by
    ext i j
    by_cases e : i = j
    · subst j
      rw [Matrix.one_apply_eq]
      change M _ _=_
      have hU : M (f i) (g i)=M x y :=
        hh x.2 y.2 _ _ x.1 y.1 (Finset.union_sdiff_of_subset (hi i).1)
      rw [hU]; exact (bit_cases _).resolve_left hxy
    rw [Matrix.one_apply_ne e]
    change M (f i) (g j)=0
    by_contra H
    have hl := Nat.find_min' hD (show D _ from ⟨f i,g j,H,rfl⟩)
    rw [← hw] at hl
    change d ≤ (i.val ∪ (U \ j.val)).card at hl
    have heq : i.val∪(U \ j.val) = U :=
      Finset.eq_of_subset_of_card_le (union_subset (hi i).1 sdiff_subset) hl
    have hsub : j.val⊆i.val := by
      intro a ha
      have hj := (hi j).1 ha
      rw [← heq] at hj
      exact (mem_union.mp hj).resolve_right (fun h => (mem_sdiff.mp h).2 ha)
    exact e (Subtype.ext (Finset.eq_of_subset_of_card_le hsub
      (by rw [(hi i).2,(hi j).2])).symm)
  have hK := M.rank_submatrix_le f g
  rw [hf, Matrix.rank_one,Fintype.card_coe] at hK
  dsimp only [T] at hK; rw [card_powersetCard] at hK
  have hv := Nat.choose_le_middle 1 d
  rw [Nat.choose_one_right] at hv
  exact Nat.not_lt_of_le ((hv.trans hK).trans hr) hd

theorem mrk_sum_le {I J A : Type} [Fintype I] [Fintype J] (s : Finset A) (f : A → Mat I J) :
    (∑ i∈s,f i).rank ≤ ∑ i∈s,(f i).rank := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s h ih =>
    rw [Finset.sum_insert h,Finset.sum_insert h]
    exact le_trans (mrk_add_le _ _) (by gcongr)

theorem mput_rank_le (s : Label p.b) (A : BaseMat p n) :
    (mput p s A).rank ≤ A.rank :=
  (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

def labelSum (p : Shape) (L : Finset (Label p.b)) (Z : Label p.b → BaseMat p n) :=
  ∑ s∈L, mput p s (Z s)

set_option maxHeartbeats 800000 in
theorem label_support {M : Moment p n} (hm : M∈Wspace p n)
    (R : ℕ) (hj : 6*R+4≤p.j) (hr : M.rank ≤ R) :
    ∃ (L : Finset (Label p.b)) (Z : Label p.b → BaseMat p n),
      L.card ≤ R ∧ (∑ s∈L,(Z s).rank) ≤ R ∧ M=labelSum p L Z ∧
      ∀ s∈L,(Z s)ᵀ=Z s ∧ ∀ i,Z s i i=Z s none i := by
  classical
  obtain ⟨k,hk,hk',hh⟩ := flat_atLayer M hr hj
  let t := (atLayer M hk).rank
  let h := (Nat.le_succ k).trans hk
  obtain ⟨s,u,v,hv⟩ := flat_entries (Wspace_sym hm) (Wspace_hank hm) hk hh
  let L := Finset.univ.image s
  let S (z : Label p.b) : Finset (Fin t) := Finset.univ.filter (fun i => s i=z)
  let Z := fun z : Label p.b => ∑ i ∈ S z,vecMulVec (u i) (v i)
  have hS (i : Fin t) : s i∈L := mem_image_of_mem _ (mem_univ _)
  have ht : t≤R := (rank_atLayer_le _ _).trans hr
  have hL : L.card≤R := card_image_le.trans (by simpa [t] using ht)
  have hZ : (∑ i∈L,(Z i).rank) ≤ R := by
    have he (i : Label p.b) : (Z i).rank ≤ (S i).card := by
      refine (mrk_sum_le (S i) _).trans ((sum_le_sum (g:=fun _ => (1:ℕ))
        (fun j _ => Matrix.rank_vecMulVec_le (u j) (v j))).trans_eq ?_)
      simp
    refine le_trans (sum_le_sum (fun i _ => he i)) ?_
    have hx : (∑ i∈L,(S i).card) = (Finset.univ : Finset (Fin t)).card :=
      (Finset.card_eq_sum_card_fiberwise (fun i _ => hS i)).symm
    rw [hx,Finset.card_univ,Fintype.card_fin]; exact ht
  refine ⟨L,Z,hL,hZ,?_⟩
  let T := labelSum p L Z
  have hrT : T.rank ≤ R := (mrk_sum_le L _).trans
    ((sum_le_sum (fun i _ => mput_rank_le i (Z i))).trans hZ)
  have he : atLayer M h=atLayer T h := by
    ext i j
    rw [hv]
    let F (x : Fin t) := monoBit (s x) i.1.val * monoBit (s x) j.1.val * (u x i.2 * v x j.2)
    change ∑ x : Fin t, F x = (∑ z∈L,mput p z (Z z)) (rise p h i) (rise p h j)
    rw [Matrix.sum_apply, ← Finset.sum_fiberwise_of_maps_to (fun i _ => hS i) F]
    refine sum_congr rfl fun x _ => ?_
    simp only [mput_apply,Z,Matrix.sum_apply,vecMulVec_apply, mul_sum,rise]
    refine sum_congr rfl fun y hy => ?_
    unfold F
    rw [(mem_filter.mp hy).2]
  have heq : M=T := by
    have hzero : M+T=0 := by
      apply zero_extension (k:=k) _ _ h
      · unfold atLayer
        ext i j
        have h1 := congr_fun (congr_fun he i) j
        change M _ _ + T _ _ = _
        change M _ _=T _ _ at h1
        rw [h1,char_two]; rfl
      · intro i j a b c d hg
        have h1 := Wspace_hank hm i j a b c d hg
        have h2 : T (a,i) (b,j)=T (c,i) (d,j) := by
          simp only [T,labelSum,Matrix.sum_apply]
          exact sum_congr rfl fun x _ => mput_hank x _ i j a b c d hg
        simp only [Matrix.add_apply,h1,h2]
      · refine (mrk_add_le _ _).trans ?_; omega
    exact add_right_cancel (hzero.trans (char_two T).symm)
  refine ⟨heq,?_⟩
  have heA i j (b : SelIdx p.b p.j) :
      M (b,i) (emptySel,j) = ∑ s∈L,Z s i j*monoBit s b.val ∧
      M (emptySel,i) (b,j) = ∑ s∈L,Z s i j*monoBit s b.val := by
    rw [heq]
    simp only [T,labelSum,Matrix.sum_apply,mput_apply]
    simp only [monoBit,emptySel,Finset.prod_empty,mul_one,mul_comm]
    simp
  have hint (i j k l : AIdx p.g n)
      (h : ∀ b : SelIdx p.b p.j,
        ∑ s∈L,Z s i j*monoBit s b.val=∑ s∈L,Z s k l*monoBit s b.val) :
      ∀ s∈L,Z s i j = Z s k l := by
    intro s hs
    have he := selector_indep L (fun s => Z s i j-Z s k l) p.j (by omega) (by
      intro U hU
      simp only [sub_mul,Finset.sum_sub_distrib]
      exact sub_eq_zero.mpr (h ⟨U,hU⟩)) s hs
    exact sub_eq_zero.mp he
  intro s hs
  constructor
  · ext i j
    apply hint j i i j _ s hs
    intro b
    rw [← (heA j i b).1,← (heA i j b).2]
    exact congr_fun (congr_fun (Wspace_sym hm) _) _
  intro i
  apply hint i i none i _ s hs
  intro b
  rw [← (heA i i b).1,← (heA none i b).1]
  exact Wspace_diag hm _ _ _

end HadwigerCounterexample

end

end OAI
