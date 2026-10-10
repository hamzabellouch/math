import OAI.Combinatorics.HadwigerCounterexample.FrameRotations

namespace OAI

/-! # Random Linear Transforms -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Submodule Finset Function
open scoped BigOperators
variable {I J K : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype K] [DecidableEq K]

namespace Move

instance finiteMove (I : Type) [Fintype I] [DecidableEq I] : Fintype (Move I) := by
  classical
  let S := { z : Mat I I × Mat I I // z.1*z.2 = 1 ∧ z.2*z.1=1}
  let e : S ≃ Move I := {
    toFun z := ⟨z.val.1,z.val.2,z.property.1,z.property.2⟩
    invFun z := ⟨(z.L,z.R),z.LR,z.RL⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  exact Fintype.ofEquiv S e

instance identity_move (I : Type) [Fintype I] [DecidableEq I] : Nonempty (Move I) :=
  ⟨1,1, Matrix.one_mul _,Matrix.mul_one _⟩
def combine (c d : Move I) : Move I :=
  ⟨c.L*d.L,d.R*c.R,by rw [Matrix.mul_assoc,←Matrix.mul_assoc d.L,d.LR,Matrix.one_mul,c.LR],
    by rw [Matrix.mul_assoc,←Matrix.mul_assoc c.R,c.RL,Matrix.one_mul,d.RL]⟩

@[ext] theorem extn (p q : Move I) (h : p.L=q.L) (h' : p.R=q.R) : p=q := by
  cases p; cases q; cases h; cases h'; rfl
def circShift (c : Move I) : Move I≃ Move I where
  toFun := combine c
  invFun := combine c.sym
  left_inv d := extn _ _ (by simp only [combine,sym,←Matrix.mul_assoc,c.RL, Matrix.one_mul])
    (by simp only [combine,sym,Matrix.mul_assoc,c.RL, Matrix.mul_one])
  right_inv d := extn _ _ (by simp only [combine,sym,←Matrix.mul_assoc,c.LR, Matrix.one_mul])
    (by simp only [combine,sym,Matrix.mul_assoc,c.LR, Matrix.mul_one])
def flipLines (I : Type) [Fintype I] [DecidableEq I] : Move I≃ Move I where
  toFun := Move.dual
  invFun := Move.dual
  left_inv _ := rfl
  right_inv _ := rfl

theorem flit_obs (M : Mat I J) (h : Injective M.mulVec) :
    mapW unif (fun c : Move I => c.L*M)=unifOn (fun A => Injective A.mulVec) := by
  classical
  rw [← unifOn_true]
  refine uniform_orbit _ (by obtain ⟨i⟩ := identity_move I; exact ⟨i,trivial⟩)
    (fun x _ => inj_comp_mat _ _ x.L_inj h) ?_
  intro x y hx hy
  obtain ⟨c,hc⟩ := move_exists_one hx hy
  refine ⟨circShift c,fun _ => Iff.rfl,fun w => ?_⟩
  change w.L*M=x ↔ c.L*w.L*M=y
  rw [←hc,Matrix.mul_assoc]; exact (c.permMat J).injective.eq_iff.symm

theorem flit_pmax (M Q : Mat I J) (h : Injective M.mulVec)
    (ha : num J-num I≤ -1) :
    pr unif (fun c : Move I => c.Rᵀ*M=Q) ≤ 2*bp (-num I*num J) := by
  let P (M : Mat I J) := Injective M.mulVec
  have ht :
      pr unif (fun c : Move I=> c.Rᵀ*M=Q)=unifOn P Q := by
    change pr unif (fun x : Move I => (flipLines I x).L*M=Q)=_
    rw [← mapW_pr unif (flipLines I) (fun c => c.L*M=Q),unif_equiv]
    exact congr_fun (flit_obs M h) Q
  have hh : 2⁻¹ ≤ pr unif P := by
    have hv := @unif_fail J I _ _ _ _
    rw [pr_not,unif_law.total] at hv
    have he := bp_le ha
    rw [bp_neg,bp_one] at he; change 1-pr unif P ≤ _ at hv; linarith only [hv,he]
  rw [ht,←on_unif]
  have he : unif Q=bp (-num I*num J) := by rw [unif_apply,neg_mul,bp_neg,←cast_mat]
  exact (on_mon unif_law.nz (show 0<(2:ℝ)⁻¹ from by norm_num) hh Q).trans_eq
    (by rw [he,inv_inv])

variable {n : ℕ}
def plume {n : ℕ} (c : Flit n) (S : Space (Vec (Fin n))) :=
  colSp (c.Rᵀ*pack S)

theorem plume_dim (c : Flit n) (S : Space (Vec (Fin n))) : dim (plume c S)=dim S := by
  have hh := mrk_inj.mp (inj_comp_mat c.Rᵀ _ c.dual.L_inj (pack_inj S))
  rw [plume,colSp_dim,hh,Fintype.card_fin]

omit [Fintype I] [DecidableEq I] [DecidableEq J] [DecidableEq K] in
private theorem smaller_cols (P : Mat I J) (Q : Mat I K) (h : colSp P ≤ colSp Q) :
    ∃ M : Mat K J,Q*M=P := by
  classical
  choose f hf using fun i : J =>
    show ∃ z : Vec K,Q *ᵥ z=P.col i from h (colSp_mem i)
  refine ⟨Matrix.of (fun i j => f j i),?_⟩
  ext i j; exact congr_fun (hf j) i

set_option maxHeartbeats 800000 in
theorem plume_meets (n a : ℕ) (ha : a<n) (U V : Space (Vec (Fin n))) :
    pr unif (fun c : Flit n => a≤dim (c.plume U ⊓ V : Space (Vec (Fin n))))≤
      bp (1+((dim U:ℝ)+dim V-n)*a) := by
  classical
  let P := Mat (Fin (dim U)) (Fin a); let Q := Mat (Fin (dim V)) (Fin a)
  let S (z : P×Q) := pack U*z.1
  let q (p : P × Q) (c : Flit n) :=
    Injective (S p).mulVec∧c.Rᵀ*S p=pack V*p.2
  have hi (c : Flit n) (hc : a≤dim (c.plume U ⊓ V : Space (Vec (Fin n)))) :
      ∃ i,q i c := by
    let w := c.plume U⊓V
    obtain ⟨M,hM,hg⟩ := bounded_pack w a
    have he : Injective M.mulVec := mrk_inj.mpr (by
      rw [← colSp_dim,hg,Fintype.card_fin,min_eq_right hc])
    have hU := le_trans hM (show w≤c.plume U from inf_le_left)
    have hV : colSp M ≤ colSp (pack V) := by rw [colSp_pack]; exact le_trans hM inf_le_right
    obtain ⟨P,hp⟩ := smaller_cols _ _ hU
    obtain ⟨Q,hq⟩ := smaller_cols _ _ hV
    rw [Matrix.mul_assoc] at hp
    refine ⟨(P,Q),?_,hp.trans hq.symm⟩
    have hx (z : Vec (Fin a)) :
        c.Rᵀ*ᵥ((pack U * P)*ᵥz)= M*ᵥz := by rw [mulVec_mulVec,hp]
    intro i j hg; exact he ((hx i).symm.trans ((congrArg _ hg).trans (hx j)))
  have ht (i : P × Q) :
      pr unif (q i) ≤2*bp (-(n:ℝ)*a) := by
    by_cases h : Injective (S i).mulVec
    · unfold q; simp only [h,true_and]
      have hx : num (Fin a)-num (Fin n) ≤ -1 := by
        simp only [num,Fintype.card_fin]
        have hi : (a:ℝ)+1≤n := by exact_mod_cast ha
        linarith only [hi]
      simpa only [num,Fintype.card_fin] using flit_pmax (S i) (pack V*i.2) h hx
    simp only [q,h,false_and,pr_false]
    exact mul_nonneg (by norm_num) (bp_pos _).le
  refine (le_trans (pr_mono unif_law.nz hi) (pr_exists_le unif_law.nz q)).trans
    ((sum_le_sum (fun i _ => ht i)).trans_eq ?_)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_prod,Nat.cast_mul]
  change num P*num Q* _=_
  unfold P Q; rw [cast_mat,cast_mat,←bp_one,←bp_add,←bp_add,←bp_add]
  congr 1; simp only [num,Fintype.card_fin]; ring
end Move
end HadwigerCounterexample

end

end OAI
