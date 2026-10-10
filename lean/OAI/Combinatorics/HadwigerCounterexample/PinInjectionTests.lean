import OAI.Combinatorics.HadwigerCounterexample.PhaseParameters

namespace OAI

/-! # Pin Injection Tests -/

noncomputable section
namespace HadwigerCounterexample

open Matrix LinearMap Module Submodule Finset Function
open scoped BigOperators
variable {p : Shape} {n N : ℕ}

abbrev Fpins (p : Shape) (n N : ℕ) := UnitType p n N → Plan p n

def rootSet (b : Fpins p n N) (x : UnitType p n N) (i : Bool) (z : Place p) :
    Space (Vec (Fin N)) :=
  (sPin (b x) z i).map (fpAt p (onSide x i) z).mulVecLin

theorem rootSet_dim (b : Fpins p n N) (x : UnitType p n N) (i : Bool) (z : Place p) :
    dim (rootSet b x i z)≤planRank (b x) :=
  (Submodule.finrank_map_le ..).trans ((sPin_dim ..).trans (dim_le_plan ..))

theorem rootSet_subset (b : Fpins p n N) (x : UnitType p n N) (i : Bool) (z : Place p) :
    rootSet b x i z ≤ imageP p x i z := by
  rintro y ⟨v,hv,rfl⟩
  exact ⟨v,rfl⟩

def strikeH (b : Fpins p n N) (z : Place p) (j : Bool) (v : Vec (Fin N)) (y : UnitType p n N) :=
  (fyAt p (onSide y j) (flipZ p z))ᵀ*ᵥ v∈ hPin (b y) z j
def fans (b : Fpins p n N) (z : Place p) (i j : Bool) (x y : UnitType p n N) :=
  ∃ v∈rootSet b x i z,v≠0 ∧ strikeH b z j v y

theorem fans_of_not_inj (b : Fpins p n N) (x y : UnitType p n N) (m : Mixer p n)
    (hh : ∀ i,frameLaw m (onSide x i))
    (h : ¬tableInj (b x) (b y) (actual p x y)) :
    ∃ z i j, fans b z i j x y := by
  unfold tableInj at h
  push Not at h
  obtain ⟨z,i,j,v,hv,he,hg⟩ := h
  let B := fpAt p (onSide x i) z
  have hf : v∈sPin (b x) z i := ⟨_,hv,(by
    change (IP p n i)ᵀ *ᵥ (IP p n i *ᵥ v) = v
    rw [Matrix.mulVec_mulVec,IP_self,Matrix.one_mulVec])⟩
  have ht : Injective B.mulVec := by
    cases z with
    | mk e c =>
      cases c; exact primary_inj (hh i e).2.1; exact primary_inj (hh i e).1
  refine ⟨z,i,j,B *ᵥ v,⟨v,hf,rfl⟩, fun hx => hg (ht (hx.trans (Matrix.mulVec_zero _).symm)),?_⟩
  have hZ :
      channelOut p (actual p x y) j z * IP p n i=(fyAt p (onSide y j) (flipZ p z))ᵀ*B := by
    unfold channelOut actual
    rw [Matrix.mul_assoc (images x z)ᵀ,images_ih,Matrix.transpose_mul,Matrix.transpose_transpose,
      Matrix.mul_assoc,images_ip]; rfl
  rw [Matrix.mulVec_mulVec,hZ,← Matrix.mulVec_mulVec] at he
  exact he

def fireBill (p : Shape) (k K : ℕ) (H : ℝ) :=
  H*2 * bp ((p.h:ℝ)*K+(K-(p.h:ℝ))*k)

set_option maxHeartbeats 600000 in
theorem strikers (b : Fpins p n N) (K : ℕ) (hb : ∀ x,planRank (b x)≤K)
    {k : ℕ} (P : Mat (Fin N) (Fin k)) (h : Injective P.mulVec)
    {w : Wgt (UnitType p n N)} (m : Mixer p n) {H : ℝ} (hH : 0 ≤ H)
    (hh : bySide p w m H) (hw : SubLaw w) (i : Bool) (z : Place p) (hN : 2*num (Full p n)-N≤ -1) :
    pr w (fun y => ∀ j,strikeH b z i (P.col j) y) ≤ fireBill p k K H := by
  classical
  let f (y : UnitType p n N) := (fyAt p (onSide y i) (flipZ p z))ᵀ*P
  have hh' y (hh : ∀ j,strikeH b z i (P.col j) y) :
      colSp (f y)≤ hPin (b y) z i := by
    rw [colSp, range_mulVecLin]
    exact Submodule.span_le.mpr (Set.range_subset_iff.mpr fun j => hh j)
  let A := Mat (Chan p) (Fin K)
  let D := Mat (Fin K) (Fin k)
  have he y (hh : ∀ j,strikeH b z i (P.col j) y) :
      ∃ v : A×D, f y=v.1 * v.2 := by
    have hr : (f y).rank ≤ K :=
      (Submodule.finrank_mono (hh' y hh)).trans
        (((hPin_dim ..).trans (dim_le_plan ..)).trans (hb y))
    obtain ⟨Q,X,hQ⟩ := mul_factor (f y) K hr
    exact ⟨(Q,X),hQ.symm⟩
  let C (v : A×D) (x) := f x=v.1*v.2
  refine ((pr_mono hw.nz he).trans (pr_exists_le hw.nz C)).trans ?_
  have ht v :
      pr w (C v)≤H*2* (bp (-(p.h:ℝ)*k)) := by
    have he := test_transpose m hH hh i (flipZ p z) hN P h (v.1*v.2)
    rw [unif_apply,card_space,dim_mat] at he
    exact he.trans_eq (by rw [neg_mul,bp_neg]; simp)
  refine (Finset.sum_le_sum fun i _ => ht i).trans_eq ?_
  rw [Finset.sum_const,nsmul_eq_mul,card_univ,Fintype.card_prod,Nat.cast_mul]
  have hA : num A=bp ((p.h:ℝ)*K) := by simp only [A,cast_mat,Chan,num,Fintype.card_fin]
  have hD : num D=bp ((K:ℝ)*k) := by simp only [D,cast_mat,num,Fintype.card_fin]
  unfold fireBill
  change num A*num D*_ = _
  rw [hA,hD,←bp_add, mul_left_comm,←bp_add]; congr 2; ring

end HadwigerCounterexample

end

end OAI
