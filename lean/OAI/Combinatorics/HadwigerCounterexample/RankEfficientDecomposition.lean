import OAI.Combinatorics.HadwigerCounterexample.DerivativeCompression

namespace OAI

/-! # Rank Efficient Decomposition -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Finset
open scoped BigOperators
variable {p : Shape} {n : ℕ} {I : Type} [Fintype I]

/-- Evaluation of individual matrices on Xpair -/
def obsI (p : Shape) {n} : Individual p n →ₗ[F] ReqF p n where
  toFun A := combineF p (repF p A)
  map_add' A B := by
    rw [←map_add]; apply congrArg
    funext i; refine LinearMap.ext fun x => ?_
    change repF p (A+B) i x= repF p A i x+ repF p B i x
    rw [repF_rep, repF_rep,repF_rep]
    simp only [Pi.add_apply,mpair_add,Finset.sum_add_distrib]
  map_smul' a A := by
    change combineF p (repF p (a•A))=a • _
    rw [←map_smul]; apply congrArg
    funext i; refine LinearMap.ext fun x => ?_
    change repF p (a•A) i x= a • (repF p A i x)
    rw [repF_rep,repF_rep]
    simp only [Pi.smul_apply,mpair_smul,smul_eq_mul,Finset.mul_sum]

theorem obsI_each (P : PureForms p n) :
    obsI p (eachF p P)=obsPair p P :=
  (obsPair_each P).symm

private theorem mrk_sub {I J : Type} [Fintype I] [Fintype J] (A B : Mat I J) :
    (A-B).rank ≤ A.rank+B.rank := by rw [ZModModule.sub_eq_add]; exact mrk_add_le A B

theorem primary_initial (M : Individual p n) (f : Plan p n) (H R : ℕ)
    (hF : ∀ z i,dim (sPin f z i) ≤ H) (hR : ∀ i e, (M i e).rank≤R) :
    ∃ P∈pureSpace p f, (∀ e,(P e).rank ≤ 2*R) ∧
      (∀ i e, ((M-eachF p P) i e).rank≤2*H) := by
  classical
  let S := sPin f
  choose A hA using fun z i => proj_exists (S z i) ⊥ disjoint_bot_right
  let B (z i) := 1-A z i
  let T : Individual p n := fun i e => pullM (B (e,true) i) (B (e,false) i) (M i e)
  refine ⟨sumF p T,?_,fun e => ?_, fun i e => ?_⟩
  · refine (pureSpace_mem _).mpr fun e => ?_
    apply Submodule.sum_mem
    intro i _
    let P z := B (e,z) i * (IP p n i)ᵀ
    have he (z : Bool) (x : Dir p n) (hx : x∈f (e,z)) : P z *ᵥ x=0 := by
      unfold P B
      let y := (IP p n i)ᵀ *ᵥ x
      have hh : y∈ S (e,z) i := ⟨_,hx,rfl⟩
      rw [←Matrix.mulVec_mulVec,Matrix.sub_mulVec,Matrix.one_mulVec]
      change y - A (e,z) i *ᵥ y=0
      rw [(hA _ _).fixes _ hh,sub_self]
    have hh : liftM (IP p n i) (IP p n i) (T i e)=(P true)ᵀ * M i e * P false := by
      simp only [liftM_def,T,pullM_def,P,Matrix.transpose_mul,Matrix.transpose_transpose,
        Matrix.mul_assoc]
    rw [hh,box_kill]
    constructor
    · intro x hx
      simp only [transpose_mul,transpose_transpose,←mulVec_mulVec,he true x hx,mulVec_zero]
    intro x hx
    rw [← Matrix.mulVec_mulVec,he false x hx,mulVec_zero]
  · refine (mrk_sum_le ..).trans ?_
    have ht i : (liftM (IP p n i) (IP p n i) (T i e)).rank≤R := (rank_lift_le ..).trans
      ((rank_lift_le ..).trans (hR i e))
    exact (Fintype.sum_bool _).le.trans ((Nat.add_le_add (ht _) (ht _)).trans_eq (two_mul R).symm)
  · rw [each_sumF]
    let z : Place p := (e,true)
    let z' : Place p := (e,false)
    let C := M i e
    change (C-(T i e)).rank≤2*H
    have he : C-T i e=(A z i)ᵀ*C+(B z i)ᵀ*C*A z' i := by
      unfold T; rw [pullM_def]
      dsimp only [B]
      simp only [transpose_sub,Matrix.transpose_one,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,
        Matrix.one_mul,C,z,z']
      abel
    have hh (z) : (A z i).rank ≤ H := (rank_maps (S z i) ((hA z i).onto)).trans (hF z i)
    rw [he,two_mul]
    refine (mrk_add_le ..).trans ?_
    exact Nat.add_le_add ((Matrix.rank_mul_le_left ..).trans (Matrix.rank_transpose (A z i) ▸ hh z))
      ((Matrix.rank_mul_le_right ..).trans (hh z'))

set_option maxHeartbeats 800000 in
theorem split_linear {M : Individual p n} {f b : Plan p n} {j : Bool}
    {C D : ChanOut p n} {P : PureForms p n}
    (R T H : ℕ) (ht : ∀ z i,dim (sPin f z i)≤T) (hm : ∀ i e,(M i e).rank≤R)
    (hc : outSmall H C)
    (hd : D∈deltaSpace p f b j) (hp : P∈pureSpace p f)
    (hh : obsPair p (chanInner p C C)+obsPair p (chanDeriv p C D)+obsPair p P=obsI p M) :
    ∃ (B : ChanOut p n) (P' P0 : PureForms p n) (Mr : Individual p n),
      B∈deltaSpace p f b j ∧ P'∈pureSpace p f ∧ P0∈pureSpace p f ∧
      outSmall (3*H) (C+B) ∧ (∀ e,(P0 e).rank≤2*R) ∧
      obsPair p (chanInner p (C+B) (C+B))+obsPair p (P'+P0)=obsI p M ∧
      obsPair p P'=obsI p Mr ∧ ∀ i e, (Mr i e).rank ≤2*T+3*H := by
  classical
  obtain ⟨B,hB,hK,hZ⟩ := deriv_compress hc hd
  obtain ⟨P0,hQ,hA,hL⟩ := primary_initial M f T R ht hm
  let P' := P-chanInner p B B-P0
  let CI := chanInner p (C+B) (C+B)
  let E := eachF p CI
  refine ⟨B,P',P0,M-eachF p P0-E,hB,(pureSpace p f).sub_mem
    ((pureSpace p f).sub_mem hp (chanInner_pure hB hB)) hQ,hQ,?_⟩
  have hsmall : outSmall (3*H) (C+B) := by
    intro z i
    rw [Pi.add_apply,Matrix.add_mul]
    apply le_trans (mrk_add_le ..)
    exact (Nat.add_le_add (hc z i) ((Matrix.rank_mul_le_left ..).trans (hK z))).trans
      (by omega)
  have hg : obsPair p (chanInner p (C+B) (C+B)) + obsPair p (P'+P0)=obsI p M := by
    rw [obsPair_chan_change,←hZ,show P'=P-chanInner p B B-P0 from rfl,sub_add_cancel,map_sub]
    exact (show _=obsPair p (chanInner p C C)+obsPair p (chanDeriv p C D)+obsPair p P by
      abel).trans hh
  refine ⟨hsmall,hA,hg,?_,fun i e => ?_⟩
  · rw [map_sub (obsI p) (M-eachF p P0) E,map_sub (obsI p),← hg]
    rw [obsI_each,show E= eachF p CI from rfl,obsI_each]
    unfold CI
    rw [map_add]; abel
  rw [Pi.sub_apply,Pi.sub_apply]
  exact (mrk_sub ..).trans (Nat.add_le_add (hL i e) (show (E i e).rank≤_ from by
    unfold E CI; rw [each_chan_val]; exact (Matrix.rank_mul_le_right ..).trans (hsmall _ i)))
end HadwigerCounterexample

end

end OAI
