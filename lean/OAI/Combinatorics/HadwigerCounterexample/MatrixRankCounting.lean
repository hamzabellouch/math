import OAI.Combinatorics.HadwigerCounterexample.MatrixFactorization
import OAI.Combinatorics.HadwigerCounterexample.FrameIntersectionBounds

namespace OAI

/-! # Matrix Rank Counting -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap
open scoped BigOperators

theorem cast_mat (I J : Type) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] :
    num (Mat I J)=bp (num I*num J) := by
  unfold num
  rw [card_space,dim_mat]
  push_cast; rfl

theorem nbr_nonneg {A : Type} [Fintype A] (p : A → Prop) : 0 ≤ nbr p :=
  tot_nonneg fun _ => ind_nonneg _

theorem nbr_le_sum {A B : Type} [Fintype A] [Fintype B] (p : A → Prop)
    (q : B → A → Prop) (h : ∀ i, p i → ∃ j,q j i) :
    nbr p ≤ ∑ j, nbr (q j) := by
  have hp (p : A → Prop) : nbr p = pr (fun _ => 1) p := by simp [nbr,pr,avg,tot]
  rw [hp]
  simp_rw [hp]
  exact (pr_mono (fun _ => zero_le_one) h).trans (pr_exists_le (fun _ => zero_le_one) q)

variable {I J K : Type} [Fintype I] [Fintype J] [Fintype K]
    [DecidableEq I] [DecidableEq J] [DecidableEq K]

omit [DecidableEq I] [DecidableEq J] in
theorem mul_factor (M : Mat I J) (r : ℕ) (h : M.rank ≤ r) :
    ∃ A : Mat I (Fin r),∃ B : Mat (Fin r) J,A*B=M := by
  obtain ⟨A,B,_,_,hg⟩ := rank_product M
  obtain ⟨a,ha⟩ := pad_matrix_inj M.rank r h
  obtain ⟨b,hb⟩ := mat_left_inv ha
  refine ⟨A*b,a*B,?_⟩
  rw [←Matrix.mul_assoc,Matrix.mul_assoc A b,hb,Matrix.mul_one,hg]

theorem nbr_matrix_rank (k : ℕ) :
    nbr (fun M : Mat I J => M.rank ≤ k) ≤ bp ((num I+num J)*k) := by
  classical
  let v := Mat I (Fin k) × Mat (Fin k) J
  let q (x : Mat I (Fin k) × Mat (Fin k) J) (M : Mat I J) := x.1*x.2=M
  refine (nbr_le_sum _ q fun M h => ?_).trans_eq ?_
  · obtain ⟨A,B,hB⟩ := mul_factor M k h
    exact ⟨(A,B),hB⟩
  have h (x : Mat I (Fin k) × Mat (Fin k) J) : nbr (q x) = 1 := by
    unfold nbr tot
    rw [Finset.sum_eq_single (x.1*x.2)]
    · simp [q,ind]
    · intro j _ h; simp [q,ind,h.symm]
    · simp
  simp_rw [h]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,mul_one]
  change num (Mat I (Fin k) × Mat (Fin k) J)=_
  rw [num,Fintype.card_prod,Nat.cast_mul]
  change num (Mat I (Fin k))*num (Mat (Fin k) J)=_
  rw [cast_mat,cast_mat,← bp_add]
  simp [num]
  ring_nf

theorem pr_matrix_rank (k : ℕ) :
    pr unif (fun M : Mat I J => M.rank≤ k) ≤
      bp ((num I+num J)*k-num I*num J) := by
  rw [pr_unif,bp_sub, ← cast_mat]
  exact div_le_div_of_nonneg_right (nbr_matrix_rank k) (Nat.cast_nonneg _)

def rmult (I : Type) (A : Mat J K) : Mat I J →ₗ[F] Mat I K where
  toFun M := M*A
  map_add' _ _ := Matrix.add_mul _ _ _
  map_smul' _ _ := Matrix.smul_mul _ _ _

theorem pr_mult_mat {A : Mat J K} (h : Function.Injective A.mulVec) (B : Mat I K) :
    pr unif (fun M => M*A=B) = bp (-num I*num K) := by
  obtain ⟨P,hP⟩ := mat_left_inv h
  have hh : Function.Surjective (rmult I A) :=
    fun C => ⟨C*P,by change C*P*A=C; rw [Matrix.mul_assoc,hP,Matrix.mul_one]⟩
  change mapW unif (rmult I A) B = _
  rw [map_unif_surjective _ hh, unif_apply, neg_mul,bp_neg,←cast_mat]

theorem pr_deficient (k : ℕ) :
    pr unif (fun M : Mat I J => M.rank + k ≤ Fintype.card J) ≤
      bp ((num J-num I)*k) := by
  classical
  let p (A : Mat J (Fin k)) (M : Mat I J) :=
    Function.Injective A.mulVec ∧ M*A=0
  refine ((pr_mono unif_law.nz fun M hm => ?_).trans
    (pr_exists_le unif_law.nz p)).trans ?_
  · let S := LinearMap.ker M.mulVecLin
    have hx := M.mulVecLin.finrank_range_add_finrank_ker
    change M.rank+dim S=dim (Vec J) at hx
    rw [dim_vec] at hx
    have hle : k ≤ dim S := Nat.le_of_add_le_add_left (hm.trans_eq hx.symm)
    obtain ⟨A,hA,h'⟩ := bounded_pack S k
    refine ⟨A,Matrix.mulVec_injective_iff.mpr ?_,?_⟩
    · apply Matrix.mulVec_injective_iff.mp
      apply mrk_inj.mpr
      rw [← colSp_dim,h',min_eq_right hle,Fintype.card_fin]
    apply coe_mv_inj
    change (M*A).mulVecLin = Matrix.mulVecLin 0
    rw [Matrix.mulVecLin_mul,Matrix.mulVecLin_zero]
    exact LinearMap.ext fun x => hA (show A.mulVecLin x ∈ colSp A from ⟨x,rfl⟩)
  have h (A : Mat J (Fin k)) : pr unif (p A) ≤ bp (-num I*k) := by
    by_cases hh : Function.Injective A.mulVec
    · simp only [p,hh,true_and]
      rw [pr_mult_mat hh]
      simp [num]
    simp only [p,hh,false_and,pr_false]
    exact (bp_pos _).le
  apply (Finset.sum_le_sum fun i _ => h i).trans_eq
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  change num (Mat J (Fin k))*_ = _
  rw [cast_mat,←bp_add]
  congr 1
  unfold num; rw [Fintype.card_fin]; ring

variable (p : Shape)
def profileA (K : ℕ) := 10*(K+1)*psize p*(p.g*p.g+5)

theorem nbr_profile_rank (K n : ℕ) :
    let d := Fintype.card (Row p n)
    nbr (fun M : Profile p n => totalRank M ≤ K) ≤
      (K+1:ℝ)^Fintype.card (Comp p.g) * bp (2*d*K) := by
  classical
  intro d
  let q (r : Comp p.g → Fin (K+1)) (M : Profile p n) :=
    (∑ i,(r i).val) ≤ K ∧ ∀ i, (M i).rank=(r i).val
  refine le_trans (nbr_le_sum _ q ?_) ?_
  · intro M h
    have hh i : (M i).rank≤K :=
      (Finset.single_le_sum (s:=Finset.univ) (fun i _ => Nat.zero_le ((M i).rank))
        (Finset.mem_univ i)).trans h
    exact ⟨fun i => ⟨_,Nat.lt_succ_of_le (hh i)⟩,h,fun _ => rfl⟩
  have he r : nbr (q r) ≤ bp (2*d*K) := by
    by_cases h : (∑ i:Comp p.g, (r i).val) ≤ K
    · unfold nbr
      let c (i : Comp p.g) (M : Moment p n) := (M.rank=(r i).val)
      simp_rw [q,h,true_and,ind_all]
      change tot (prodW (β:=fun _ => Moment p n) (fun i M => ind (c i M))) ≤ _
      rw [prodW_tot]
      have hx i : nbr (c i) ≤ bp (2*d*(r i).val) := by
        let w := (r i).val
        have h1 := nbr_matrix_rank (I:=Row p n) (J:=Row p n) w
        rw [← two_mul] at h1
        exact le_trans (tot_mono (fun x => ind_mono (p:=x.rank=w) (q:=x.rank≤w) (fun e => e.le))) h1
      refine (Finset.prod_le_prod₀ (fun i _ => nbr_nonneg (c i)) (fun i _ => hx i)).trans ?_
      rw [←bp_sum,← Finset.mul_sum, ← Nat.cast_sum]
      apply bp_le
      gcongr
    · simp only [q,h,false_and,nbr,tot,ind_false,Finset.sum_const_zero]
      exact (bp_pos _).le
  refine (Finset.sum_le_sum fun i _ => he i).trans_eq ?_
  simp

open Filter
theorem profile_count (K : ℕ) :
    ∀ᶠ n : ℕ in atTop, nbr (fun M : Profile p n => totalRank M≤K) ≤ bp ((profileA p K:ℝ)*n) := by
  let B := (K+1:ℝ)^Fintype.card (Comp p.g)
  have h := bp_poly_dom_nat (a:=1) zero_lt_one B 0
  have h1 : 0 < psize p := Fintype.card_pos_iff.mpr ⟨emptySel⟩
  filter_upwards [h,eventually_ge_atTop 1] with n hn hN
  simp only [pow_zero,mul_one,one_mul] at hn
  refine le_trans (nbr_profile_rank p K n) (le_trans
    (mul_le_mul_of_nonneg_right hn.le (bp_pos _).le) ?_)
  rw [← bp_add]
  apply bp_le
  simp only [card_row, profileA]
  push_cast
  let s := psize p
  have he : 1 ≤ s := h1
  have h' :
      n+2*(s*(1+(p.g*p.g+3)*n))*K ≤ 10*(K+1)*s*(p.g*p.g+5)*n := by
    have hi : 1+(p.g*p.g+3)*n ≤ (p.g*p.g+4)*n := by nlinarith
    have hl : s*(1+(p.g*p.g+3)*n) ≤ s*((p.g*p.g+4)*n) := by gcongr
    have hh : n ≤ s*n := by nlinarith
    nlinarith only [Nat.mul_le_mul_right K hl,hh, Nat.zero_le (s*p.g*p.g*n),
      Nat.zero_le (s*n),Nat.zero_le (s*K*p.g*p.g*n),Nat.zero_le (s*K*n)]
  exact_mod_cast h'

end HadwigerCounterexample

end

end OAI
