import OAI.Combinatorics.HadwigerCounterexample.ReferenceProductTests

namespace OAI

/-! # Endpoint Gram Ranks -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module Finset Function
open scoped BigOperators
variable {I J U : Type} [Fintype I] [Fintype J] [Fintype U]
variable [DecidableEq I] [DecidableEq J] [DecidableEq U]
variable {n N : ℕ}

omit [DecidableEq I] in
theorem pr_gram_target (X : Mat U I) (G : Mat I J) :
    pr unif (fun Y : Mat U J => Xᵀ*Y=G) ≤ bp (-(X.rank:ℝ)*num J) := by
  classical
  let P := pack (colSp X)
  obtain ⟨A,h⟩ : ∃ A : Mat I (Fin (dim (colSp X))),X*A=P := by
    have h (i:Fin (dim (colSp X))) : P.col i ∈ colSp X := by
      have hh : colSp P=colSp X := colSp_pack _
      exact hh.le (colSp_mem _)
    choose f hf using fun i : Fin (dim (colSp X)) =>
      show ∃ y : Vec I,X *ᵥ y=P.col i from h i
    refine ⟨Matrix.of (fun i j => f j i),?_⟩
    ext i j; exact congr_fun (hf j) i
  have he (Y : Mat U J) (hg : Xᵀ*Y=G) : Pᵀ*Y=Aᵀ*G := by rw [←h,transpose_mul,Matrix.mul_assoc,hg]
  refine (pr_mono unif_law.nz he).trans_eq ?_
  rw [pr_gram_fixed (pack_inj _)]
  congr 1; rw [show num (Fin (dim (colSp X)))= X.rank from (by rw [num,Fintype.card_fin,colSp_dim])]

theorem pr_offset_cross (X Y : PlusRack (Fin n) N) (G W : Mat (Fin n) (Fin n)) (r : ℕ) :
    pr unif (fun Q : PlusRack (Fin n) N =>
      Yᵀ*Q=G ∧ (Xᵀ*Q+W).rank ≤ r) ≤ bp ((2*n:ℝ)*r-(fromCols X Y).rank*(n:ℝ)) := by
  classical
  let g := fromCols X Y
  let A := Mat (Fin n) (Fin n)
  let T (i : A) := i.rank ≤ r
  let f (i : A) (y : PlusRack (Fin n) N) := T i ∧ gᵀ*y=fromRows (i-W) G
  have he (y : PlusRack (Fin n) N) (h : Yᵀ*y=G ∧ (Xᵀ*y+W).rank≤r) : ∃ i,f i y := by
    refine ⟨Xᵀ*y+W,h.2,?_⟩
    unfold g; rw [transpose_fromCols,fromRows_mul,h.1,add_sub_cancel_right]
  let P := bp (-(g.rank:ℝ)*n)
  have hi (i) : pr unif (f i) ≤ ind (T i) * P := by
    by_cases h : T i
    · unfold f; simp only [h,true_and,ind_true,one_mul]
      simpa only [num,Fintype.card_fin,P] using pr_gram_target g (fromRows (i-W) G)
    simp [f,h,ind]
  refine (le_trans (pr_mono unif_law.nz he) (pr_exists_le unif_law.nz f)).trans
    ((Finset.sum_le_sum (fun i _ => hi i)).trans ?_)
  have ht := nbr_matrix_rank (I:=Fin n) (J:=Fin n) r
  rw [← Finset.sum_mul]; unfold P
  change nbr T*_ ≤ _
  refine (mul_le_mul_of_nonneg_right ht (bp_pos _).le).trans_eq ?_
  rw [← bp_add]; congr 1; simp only [num,Fintype.card_fin,g]; ring

def crossSquare (n N : ℕ) (W : Mat (Fin n) (Fin n)) (v : F)
    (x : Rack (Fin n) N × Rack (Fin n) N) :=
  x.1.1ᵀ*x.2.2+(v • (x.1.2ᵀ * x.2.1) + W)

def rankJump (X Y : PlusRack (Fin n) N) (d : ℕ) :=
  (fromCols X Y).rank + d≤2*n

set_option maxHeartbeats 800000 in
theorem shift_square (n N r d : ℕ) (X Y : PlusRack (Fin n) N)
    (G H W : Mat (Fin n) (Fin n)) (v : F)
    (hp : Injective X.mulVec) (hq : Injective Y.mulVec) :
    let p := bp (-(n:ℝ)*n)
    pr (pairW unif unif) (fun s : PlusRack (Fin n) N × PlusRack (Fin n) N =>
      (Xᵀ*s.1=G ∧ Yᵀ*s.2=H) ∧
      (crossSquare n N W v ((X,s.1),(Y,s.2))).rank≤r) ≤
        p^2 * (ind (rankJump X Y d)+bp ((2*n:ℝ)*r - (n-d:ℝ)*n)) := by
  intro p
  let f (s t : PlusRack (Fin n) N) :=
      (Xᵀ*s=G ∧ Yᵀ*t=H) ∧ (crossSquare n N W v ((X,s),(Y,t))).rank≤r
  have ha : pr unif (fun Q : PlusRack (Fin n) N => Xᵀ*Q=G)=p := by
    rw [pr_gram_fixed hp]; simp only [p,num,Fintype.card_fin]
  have hb : pr unif (fun Q : PlusRack (Fin n) N => Yᵀ*Q=H)=p := by
    rw [pr_gram_fixed hq]; simp only [p,num,Fintype.card_fin]
  let c := bp ((2*n:ℝ)*r-(n-d:ℝ)*n)
  have hc := bp_pos ((2*n:ℝ)*r-(n-d:ℝ)*n)
  change _ ≤ p^2*(ind (rankJump X Y d) + c)
  by_cases h : rankJump X Y d
  · have he := pairW_pr unif unif (fun Q : PlusRack (Fin n) N => Xᵀ*Q=G)
      (fun Q : PlusRack (Fin n) N => Yᵀ*Q=H)
    refine (pr_mono (pairW_law unif_law unif_law).nz (fun i h => h.1)).trans ?_
    rw [he,ha,hb,ind_one h]
    rw [←pow_two]
    exact le_mul_of_one_le_right (sq_nonneg _) (by change 1≤1+c; linarith only [hc])
  have hr : (2*n:ℝ)-d≤(fromCols X Y).rank := by
    unfold rankJump at h
    have hi : 2*n≤ (fromCols X Y).rank + d := by omega
    exact sub_le_iff_le_add.mpr (by exact_mod_cast hi)
  have he (s : PlusRack (Fin n) N) : pr unif (fun t => f s t) ≤ ind (Xᵀ*s=G) * (p*c) := by
    by_cases hs : Xᵀ*s=G
    · simp only [f,hs,true_and,ind_true,one_mul]
      have hg := pr_offset_cross X Y H (v • (sᵀ*Y)+W) r
      refine le_trans hg ?_
      unfold p c; rw [← bp_add]
      apply bp_le
      nlinarith only [mul_le_mul_of_nonneg_right hr (Nat.cast_nonneg n : 0≤(n:ℝ))]
    simp [f,hs,ind]
  rw [pr,pairW_avg]
  refine (avg_mono unif_law.nz he).trans ?_
  rw [avg_mul,ind_zero h,zero_add]
  change pr unif _ * _ ≤ _
  rw [ha]; exact le_of_eq (by ring)

end HadwigerCounterexample

end

end OAI
