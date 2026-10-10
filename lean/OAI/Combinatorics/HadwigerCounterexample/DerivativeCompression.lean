import OAI.Combinatorics.HadwigerCounterexample.ResponseSolvability

namespace OAI

/-! # Derivative Compression -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule
open scoped BigOperators
variable {I J : Type} [Fintype I] [Fintype J]

theorem mat_mul_fix {A : Mat I I} {B : Mat I J} (h : ∀ x∈colSp B,A *ᵥ x=x) :
    A*B=B := by
  apply coe_mv_inj
  refine LinearMap.ext fun x => ?_
  change _ *ᵥ x=_ *ᵥ _
  rw [← Matrix.mulVec_mulVec]; exact h (B *ᵥ x) ⟨x,rfl⟩

/-- Endomorphism taking V into V, preserving dot product against S,
of rank bounded by the observer space S. -/
private theorem compress_observer (V S : Space (Vec I)) :
    ∃ A : Mat I I,(∀ v∈V,A *ᵥ v∈V) ∧
      (∀ v∈V,∀ y∈S, dotProduct y (A *ᵥ v) = dotProduct y v) ∧
      A.rank≤dim S := by
  classical
  obtain ⟨Q,hQ⟩ := mat_left_inv (pack_inj V)
  let P := (pack S)ᵀ * pack V
  obtain ⟨B,hB⟩ := proj_exists (colSp Pᵀ) ⊥ disjoint_bot_right
  let A := pack V * Bᵀ * Q
  have hh (t) : A *ᵥ (pack V *ᵥ t)=pack V *ᵥ (Bᵀ *ᵥ t) := by
    simp only [A,← Matrix.mulVec_mulVec]
    rw [Matrix.mulVec_mulVec t Q,hQ, Matrix.one_mulVec]
  refine ⟨A,fun x hx => ?_,fun x hx y hy => ?_,?_⟩
  · obtain ⟨t,rfl⟩ := (pack_mem_iff x _).mp hx
    rw [hh]
    exact (pack_mem_iff ..).mpr ⟨_,rfl⟩
  · obtain ⟨t,rfl⟩ := (pack_mem_iff x _).mp hx
    obtain ⟨u,rfl⟩ := (pack_mem_iff y _).mp hy
    rw [hh]
    have he : P * Bᵀ=P := by
      have h1 := congrArg Matrix.transpose (mat_mul_fix (A:=B) hB.fixes)
      simpa only [transpose_mul,transpose_transpose] using h1
    have hg (t') : dotProduct (pack S *ᵥ u) (pack V *ᵥ t')=dotProduct u (P *ᵥ t') := by
      rw [show P=_*_ from rfl,← Matrix.mulVec_mulVec,dotProduct_transpose_mulVec,dotProduct_comm]
    rw [hg,hg,Matrix.mulVec_mulVec,he]
  · refine ((Matrix.rank_mul_le_left ..).trans (Matrix.rank_mul_le_right ..)).trans ?_
    rw [Matrix.rank_transpose]
    exact (rank_maps (colSp Pᵀ) hB.onto).trans (by
      rw [colSp_dim,Matrix.rank_transpose]
      exact P.rank_le_card_height.trans_eq (Fintype.card_fin _))

variable {p : Shape} {n : ℕ}
def priOut (p : Shape) {n} (C : ChanOut p n) (z : Place p) : Space (Vec (Chan p)) :=
  colSp (C z * IP p n true) ⊔ colSp (C z * IP p n false)
def outSmall (H : ℕ) {p : Shape} {n} (C : ChanOut p n) :=
  ∀ (z : Place p) i,(C z * IP p n i).rank≤H

theorem le_priOut (C : ChanOut p n) (z : Place p) (i) :
    colSp (C z * IP p n i)≤priOut p C z := by
  cases i; exact le_sup_right; exact le_sup_left
theorem dim_priOut {C : ChanOut p n} {H} (h : outSmall H C) (z : Place p) :
    dim (priOut p C z) ≤2*H := by
  rw [two_mul]
  exact (Submodule.finrank_add_le_finrank_add_finrank ..).trans (Nat.add_le_add (h z true) (h z false))

theorem outSmall_low {B : Cross p n} {H} (h : lowCross H B) (j : Bool) :
    outSmall H (channelOut p B j) := by
  intro z i
  rw [channelOut, Matrix.transpose_mul,Matrix.mul_assoc]
  exact (Matrix.rank_mul_le_right ..).trans (h z i)

theorem ev_duom {K : Type} [Fintype K] (P : Mat K I) (Q : Mat K J) (v : Vec I)
    (w : Vec J) :
    evmat (Pᵀ*Q) v w = dotProduct (P *ᵥ v) (Q *ᵥ w) := by
  rw [evmat,← Matrix.mulVec_mulVec,dotProduct_transpose_mulVec,dotProduct_comm]

theorem deriv_compress {C D : ChanOut p n} {f b : Plan p n} {j : Bool} {H}
    (h : outSmall H C) (hd : D∈deltaSpace p f b j) :
    ∃ B∈deltaSpace p f b j,(∀ z,(B z).rank ≤2*H) ∧
      obsPair p (chanDeriv p C D)=obsPair p (chanDeriv p C B) := by
  classical
  let S (z) := priOut p C (flipZ p z)
  let V (z) := annih (hPin b (flipZ p z) j)
  choose A hA hS hT using fun z => compress_observer (V z) (S z)
  let B := fun z : Place p => A z * D z
  have he z : colSp (D z) ≤ V z ∧ colSp (D z)ᵀ≤ annih (f z) :=
    (box_mem ..).mp ((deltaSpace_mem _).mp hd z)
  refine ⟨B,(deltaSpace_mem _).mpr ?_,fun z => ?_,?_⟩
  · intro z
    rw [box_mem]
    constructor
    · rintro x ⟨y,rfl⟩
      rw [mulVecLin_apply]
      unfold B; rw [← mulVec_mulVec]
      exact hA z _ ((he z).1 ⟨y,rfl⟩)
    · rw [colSp_kill,transpose_transpose]
      intro x hx
      have h1 : D z *ᵥ x=0 := (box_kill.mp ((deltaSpace_mem _).mp hd z)).2 _ hx
      rw [show B z=A z * D z from rfl,←mulVec_mulVec,h1,Matrix.mulVec_zero]
  · exact (Matrix.rank_mul_le_left ..).trans ((hT z).trans (dim_priOut h (flipZ p z)))
  · rw [obsPair_each,obsPair_each]
    have hE (z : Place p) (i l : Bool) (x y : Ray p n) :
        dotProduct ((C (flipZ p z) * IP p n i) *ᵥ x) ((B z * IP p n l) *ᵥ y)=
        dotProduct ((C (flipZ p z) * IP p n i) *ᵥ x) ((D z * IP p n l) *ᵥ y) := by
      let u := (C (flipZ p z)* IP p n i)*ᵥ x
      have hu : u∈S z := le_priOut _ _ _ ⟨x,rfl⟩
      let v := D z *ᵥ (IP p n l *ᵥ y)
      have hv : v∈V z := (he z).1 ⟨_,rfl⟩
      unfold B
      unfold u at hu
      rw [← Matrix.mulVec_mulVec] at hu
      simp only [← Matrix.mulVec_mulVec]
      exact hS z _ hv _ hu
    have h1 : eachF p (chanInner p C B)=eachF p (chanInner p C D) := by
      funext i e
      rw [each_chan_val, each_chan_val]
      refine evmat_ext fun x y => ?_
      rw [ev_duom, ev_duom]
      exact hE (e,false) i i x y
    have h2 : eachF p (chanInner p B C)=eachF p (chanInner p D C) := by
      funext i e
      rw [each_chan_val,each_chan_val]
      refine evmat_ext fun x y => ?_
      rw [ev_duom,ev_duom,dotProduct_comm,dotProduct_comm ((D _ * IP p n i) *ᵥ x)]
      exact hE (e,true) i i y x
    rw [chanDeriv,chanDeriv,map_add,map_add,h1,h2]

theorem chanInner_pure {C D : ChanOut p n} {f b : Plan p n} {j : Bool}
    (h : C∈deltaSpace p f b j) (h' : D∈deltaSpace p f b j) :
    chanInner p C D∈pureSpace p f := by
  classical
  refine (pureSpace_mem _).mpr (fun e => ?_)
  have h1 : ∀ x ∈ f (e,true), C (e,true) *ᵥ x=0 :=
    (box_kill.mp ((deltaSpace_mem _).mp h _)).2
  have h2 : ∀ x ∈ f (e,false), D (e,false) *ᵥ x=0 :=
    (box_kill.mp ((deltaSpace_mem _).mp h' _)).2
  rw [box_kill]
  constructor
  · intro x hx
    unfold chanInner
    rw [Matrix.transpose_mul,Matrix.transpose_transpose,←mulVec_mulVec,h1 x hx,mulVec_zero]
  intro x hx
  unfold chanInner; rw [←mulVec_mulVec,h2 x hx,mulVec_zero]

end HadwigerCounterexample

end

end OAI
