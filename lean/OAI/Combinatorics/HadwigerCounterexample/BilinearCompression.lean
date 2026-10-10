import OAI.Combinatorics.HadwigerCounterexample.PrimalSpaceCompression

namespace OAI

/-! # Bilinear Compression -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Submodule Module Finset
open scoped BigOperators

variable {p : Shape} {n : ℕ} {I J : Type} [Fintype I] [Fintype J]

def dqBound (p : Shape) (T H R : ℕ) := 2*(drow p T R+H)

private theorem pullM_fix (A : Mat I I) (P : Mat I I)
    (h : ∀ x ∈ colSp P,Aᵀ *ᵥ x=x) (h' : ∀ x∈colSp Pᵀ,Aᵀ *ᵥ x=x) :
    pullM A A P=P := by
  rw [pullM_def,mat_mul_fix h]
  have he := congrArg Matrix.transpose (mat_mul_fix h')
  simpa only [Matrix.transpose_mul,Matrix.transpose_transpose] using he

private def dualSpace (M : Profile p n) (z : Place p) :=
  colSp (if z.2 then M z.1 else (M z.1)ᵀ)
private theorem dualSpace_dim (M : Profile p n) (z : Place p) :
    dim (dualSpace M z)=(M z.1).rank := by
  cases z with
  | mk i b =>
    cases b; exact Matrix.rank_transpose _; rfl

private def jointShrink (A : Bool → Nendo p n) (B : Place p → Bool → Mat (Chan p) (Chan p))
    (z : Place p) :=
  ∑ i : Bool,(liftM (IP p n i) (IP p n i) (rowShrink p (A i))+
    liftM (IH p n i) (IH p n i) (B z i))

private theorem joint_ip (A : Bool → Nendo p n) (B : Place p → Bool → Mat (Chan p) (Chan p))
    (z : Place p) (i : Bool) :
    jointShrink A B z * IP p n i = IP p n i * rowShrink p (A i) := by
  classical
  simp only [jointShrink,Fintype.sum_bool,liftM_def,Matrix.add_mul,Matrix.mul_assoc,
    IH_IP,Matrix.mul_zero,add_zero]
  cases i <;> simp only [IP_self,IP_cross (show true≠false by decide),
    IP_cross (show false≠true by decide),Matrix.mul_zero,Matrix.mul_one,add_zero,zero_add]

set_option maxHeartbeats 800000 in
theorem shrink_pure {f : Plan p n} {M : Individual p n} {P : PureForms p n}
    (T H R : ℕ) (ht : ∀ z i,dim (sPin f z i)≤T) (hh : ∀ z i,dim (hPin f z i)≤H)
    (hr : ∀ i e,(M i e).rank≤R)
    (hp : P∈pureSpace p f) (he : obsPair p P=obsI p M) :
    ∃ Q∈pureSpace p f,obsPair p Q=obsPair p P ∧ ∀ e,(Q e).rank≤dqBound p T H R := by
  classical
  choose A hA hL hT using fun i => shrink_both (fun z => sPin f z i) (dualSpace (M i)) T R
    (fun z => ht z i) (fun z => by rw [dualSpace_dim]; exact hr i z.1)
  choose B hB using fun z i => proj_exists (hPin f z i) ⊥ disjoint_bot_right
  let D := jointShrink A B
  have hf (z : Place p) (x : Dir p n) (hx : x∈f z) : D z *ᵥ x=x := by
    have h1 (i : Bool) : rowShrink p (A i) *ᵥ ((IP p n i)ᵀ *ᵥ x)=(IP p n i)ᵀ *ᵥ x :=
      hA i z _ ⟨_,hx,rfl⟩
    have h2 (i : Bool) : B z i *ᵥ ((IH p n i)ᵀ *ᵥ x)=(IH p n i)ᵀ *ᵥ x :=
      (hB z i).fixes _ ⟨_,hx,rfl⟩
    unfold D jointShrink
    simp only [Matrix.sum_mulVec,Matrix.add_mulVec,liftM_def,← Matrix.mulVec_mulVec,h1,h2]
    exact ip_decomp x
  have hR (z : Place p) : (D z).rank ≤ dqBound p T H R := by
    apply le_trans (mrk_sum_le ..)
    have hx i :
        (liftM (IP p n i) (IP p n i) (rowShrink p (A i))+
          liftM (IH p n i) (IH p n i) (B z i)).rank ≤ drow p T R+H :=
      (mrk_add_le ..).trans (add_le_add
        ((rank_lift_le ..).trans (hT i)) ((rank_lift_le ..).trans
        ((rank_maps (hPin f z i) (hB z i).onto).trans (hh z i))))
    rw [Fintype.sum_bool,dqBound,two_mul]; exact add_le_add (hx _) (hx _)
  let Q (e : Comp p.g) := pullM (D (e,true)) (D (e,false)) (P e)
  have hG (i : Bool) (e : Comp p.g) : pullM (rowShrink p (A i)) (rowShrink p (A i)) (M i e)=
      M i e := pullM_fix _ _ (hL i (e,true)) (hL i (e,false))
  have hY (i : Bool) (e : Comp p.g) : eachF p Q i e=
      pullM (rowShrink p (A i)) (rowShrink p (A i)) (eachF p P i e) := by
    change pullM _ _ (Q e)=pullM _ _ (pullM _ _ _)
    let G := IP p n i
    have hw {I J K U V W : Type} [Fintype U] [Fintype V] [Fintype W] [Fintype I]
        [Fintype J] [Fintype K] (L : Mat U I) (R : Mat V J)
        (L' : Mat I K) (R' : Mat J W) (P : Mat U V) :
        pullM L' R' (pullM L R P) = pullM (L*L') (R*R') P := by
      unfold pullM
      rw [liftM_comp,Matrix.transpose_mul,Matrix.transpose_mul]
    unfold Q
    rw [hw,hw]
    have h (b) := joint_ip A B (e,b) i
    rw [show D (e,true)*IP p n i=_ from h true, show D (e,false)*IP p n i=_ from h false]

  refine ⟨Q,?_,?_,fun e => ?_⟩
  · refine (pureSpace_mem _).mpr fun e => ?_
    obtain ⟨h1,h2⟩ := box_kill.mp ((pureSpace_mem _).mp hp e)
    unfold Q; rw [box_kill,pullM_def]; constructor
    · intro x hx
      simp only [transpose_mul,transpose_transpose,←Matrix.mulVec_mulVec,hf (e,true) x hx,h1 x hx,
        mulVec_zero]
    intro x hx
    rw [← mulVec_mulVec,hf (e,false) x hx]
    rw [← mulVec_mulVec,h2 x hx,mulVec_zero]
  · rw [he,obsPair_each]
    rw [obsPair_each] at he
    change combineF p _=combineF p _
    change combineF p _=combineF p _ at he
    have he := (combineF_same ..).mp he
    apply (combineF_same ..).mpr
    intro i x hx
    let y : Profile p n := fun e => liftM (rowShrink p (A i)) (rowShrink p (A i)) (x e)
    rw [repF_rep,repF_rep]
    have hv := he i y (shrink_X (A i) x hx)
    rw [repF_rep,repF_rep] at hv
    have hu (F : Individual p n) : (∑ e,mpair (F i e) (y e))=
        ∑ e,mpair (pullM (rowShrink p (A i)) (rowShrink p (A i)) (F i e)) (x e) :=
      Finset.sum_congr rfl fun e _ => mpair_liftM ..
    rw [hu,hu] at hv
    simp_rw [← hY,hG] at hv
    exact hv
  unfold Q; rw [pullM_def]
  exact ((Matrix.rank_mul_le_left ..).trans (Matrix.rank_mul_le_left ..)).trans
    (by rw [Matrix.rank_transpose]; exact hR _)

end HadwigerCounterexample

end

end OAI
