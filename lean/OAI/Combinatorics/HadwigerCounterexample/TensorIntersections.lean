import OAI.Combinatorics.HadwigerCounterexample.SparseCutProfiles

namespace OAI

/-! # Tensor Intersections -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Submodule
open scoped BigOperators

variable {p : Shape} {n N : ℕ}

section Rank
variable {U I J L : Type} [Fintype I] [Fintype J] [Fintype U] [Fintype L]

omit [Fintype U] in
theorem colSp_join (A : Mat U I) (B : Mat U J) :
    colSp (fromCols A B) = colSp A ⊔ colSp B := by
  apply le_antisymm
  · rintro _ ⟨x,rfl⟩
    rw [mulVecLin_apply,fromCols_mulVec]
    exact add_mem_sup (show A *ᵥ _ ∈ colSp A from ⟨_,rfl⟩)
      (show B *ᵥ _ ∈ colSp B from ⟨_,rfl⟩)
  refine sup_le ?_ ?_
  · rintro _ ⟨x,rfl⟩
    refine ⟨Sum.elim x 0,?_⟩
    simp only [mulVecLin_apply,fromCols_mulVec_sumElim,Matrix.mulVec_zero,add_zero]
  · rintro _ ⟨x,rfl⟩
    refine ⟨Sum.elim 0 x,?_⟩
    simp only [mulVecLin_apply,fromCols_mulVec_sumElim,Matrix.mulVec_zero,zero_add]

omit [Fintype U] in
theorem colSp_primary (A : Mat U (I⊕J)) : colSp (primary A) ≤ colSp A :=
  calc colSp (primary A) ≤ colSp (primary A) ⊔ colSp (channel A) := le_sup_left
       _ = colSp A := by rw [← colSp_join,fromCols_frame]

omit [Fintype U] in
theorem join_kernel {A : Mat U I} {B : Mat U J}
    (ha : Function.Injective A.mulVec) (hb : Function.Injective B.mulVec) :
    dim (colSp A ⊓ colSp B : Submodule _ _) = dim (ker (fromCols A B).mulVecLin) := by
  have h := finrank_sup_add_finrank_inf_eq (colSp A) (colSp B)
  have h' := (fromCols A B).mulVecLin.finrank_range_add_finrank_ker
  rw [← colSp_join] at h
  change dim (colSp _) + dim _ = dim _+dim _ at h
  change dim (colSp _) + dim _ = dim _ at h'
  rw [colSp_dim A,colSp_dim B,mrk_inj.mp ha,mrk_inj.mp hb] at h
  rw [dim_vec, Fintype.card_sum] at h'
  omega

omit [Fintype U] in
theorem colSp_lift_le (P : Mat U I) (Q : Mat L J) (A : Mat I J) :
    colSp (liftM P Q A) ≤ colSp P := by
  rw [liftM_def,Matrix.mul_assoc,colSp, Matrix.mulVecLin_mul]
  exact LinearMap.range_comp_le_range _ _

omit [Fintype U] in
theorem rank_lift_le (P : Mat U I) (Q : Mat L J) (A : Mat I J) :
    (liftM P Q A).rank ≤ A.rank :=
  (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

theorem rank_lift_eq {P : Mat U I} {Q : Mat L J} (hP : Function.Injective P.mulVec)
    (hQ : Function.Injective Q.mulVec) (A : Mat I J) :
    (liftM P Q A).rank = A.rank := by
  classical
  obtain ⟨P',h1⟩ := mat_left_inv hP
  obtain ⟨Q',h2⟩ := mat_left_inv hQ
  refine le_antisymm (rank_lift_le P Q A) ?_
  have h := rank_lift_le P' Q' (liftM P Q A)
  rw [liftM_comp,h1,h2,liftM_def,Matrix.one_mul,Matrix.transpose_one,Matrix.mul_one] at h
  exact h

end Rank

/-- Sum of dimensions of the kernel of the combined plus maps at each component.
This bounds (in fact equals) the sum of intersection dimensions of full plus
frames when the frames are valid. -/
def joins (x : UnitType p n N) : ℕ :=
  ∑ i : Comp p.g, dim (ker (images x (i,true)).mulVecLin)

theorem totalRank_shared {m : Mixer p n} {x y : Orient p n N}
    (hx : frameLaw m x) (hy : frameLaw m y) {v w : Profile p n}
    (h : Uembed x v = Uembed y w) :
    totalRank v = totalRank w ∧ totalRank v ≤ joins (x,y) := by
  have he (x : Orient p n N) (hx : frameLaw m x) (a : Profile p n) (i) :
      (Uembed x a i).rank = (a i).rank :=
    rank_lift_eq (primary_inj (hx i).1) (primary_inj (hx i).2.1) (a i)
  have hf i : (v i).rank=(w i).rank := by rw [← he x hx,← he y hy,h]
  refine ⟨Finset.sum_congr rfl fun i _ => hf i, Finset.sum_le_sum fun i _ => ?_⟩
  let A := (x i).1
  let B := (y i).1
  have hi (x : Orient p n N) (v) :
      colSp (Uembed x v i) ≤ colSp (x i).1 :=
    (colSp_lift_le _ _ _).trans (colSp_primary _)
  have hh : colSp (Uembed x v i) ≤ colSp A ⊓ colSp B :=
    le_inf (hi x v) (by rw [h]; exact hi y w)
  change (v i).rank ≤ dim (ker (images _ _).mulVecLin)
  rw [← he x hx,← colSp_dim]
  apply le_trans (Submodule.finrank_mono hh)
  exact (join_kernel (hx i).1 (hy i).1).le

theorem eta_share {m : Mixer p n} {x : Orient p n N} {v : Profile p n} (hj : 1 ≤ p.j)
    (hx : frameLaw m x) (hv : v ∈ Xspace p n) (i) :
    mpair (1:Mat (Fin N) (Fin N)) (Uembed x v i) = eta p n (v i) := by
  let P := primary (x i).1
  let Q := primary (x i).2
  have hi : v i ∈ Wspace p n := by
    obtain ⟨w,hw,rfl⟩ := mem_X.mp hv
    exact Submodule.add_mem _ (Wtag_le _ (hw _)) (Wtag_le _ (hw _))
  change mpair _ (liftM P Q (v i)) = _
  rw [mpair_liftM,liftM_def,transpose_transpose, Matrix.mul_one,
    show Pᵀ*Q=selfM p n m.mixM from (hx i).2.2.1,selfM_pair _ hj _ hi]

def parityW (w : Tag p.g → Moment p n) := ∑ i, eta p n (w i)

theorem parityW_shared {m : Mixer p n} (hj : 1 ≤ p.j) {x y : Orient p n N}
    (hx : frameLaw m x) (hy : frameLaw m y) {v w : Tag p.g → Moment p n}
    (hv : ∀ l, v l∈ Wtag p n l) (hw : ∀ l, w l∈ Wtag p n l)
    (h : Uembed x (cut p n v) = Uembed y (cut p n w))
    (hv' : 2 * (nonzeroTags v).card < p.g)
    (hw' : 2 * (nonzeroTags w).card < p.g) : parityW v = parityW w := by
  have he i : eta p n (cut p n v i) = eta p n (cut p n w i) := by
    rw [← eta_share hj hx (mem_X.mpr ⟨v,hv,rfl⟩),← eta_share hj hy (mem_X.mpr ⟨w,hw,rfl⟩),h]
  obtain ⟨l,hl,hL⟩ := common_zero hv' hw'
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases htl : l=t
  · subst t; rw [hl,hL]
  have hf (w : Tag p.g → Moment p n) (h : w l=0) :
      cut p n w (edge l t htl) = w t := by
    rw [← getPair_edge l t htl (cut p n w), getPair_cut,h,zero_add]
  exact (by simpa only [hf v hl,hf w hL] using he (edge l t htl))

end HadwigerCounterexample

end

end OAI
