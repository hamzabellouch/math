import OAI.Combinatorics.HadwigerCounterexample.BinaryEvaluationForms

namespace OAI

/-! # Random Binary Mixing -/

noncomputable section
namespace HadwigerCounterexample

instance momFintype (p : Shape) (n : ℕ) : Fintype (Moment p n) := inferInstance
instance idxDec (p : Shape) : DecidableEq (MIdx p) := inferInstance
instance arrFintype (p : Shape) (n : ℕ) : Fintype (MArr p n) := inferInstance
instance drawFintype (p : Shape) (n : ℕ) : Fintype (Draw p n) := inferInstance

open Filter Matrix Function
open scoped BigOperators Topology

variable {p : Shape} {n : ℕ}

theorem rank_fifth_bound (m n : ℕ) (hm : n/2≤m) (hn : 100 ≤ n) :
    pr unif (fun M : Mat (Fin m) (Fin m) => 5*M.rank<n) ≤ bp (- (n:ℝ)) := by
  apply le_trans (pr_mono unif_law.nz (q:=fun M => M.rank≤ n/5) (fun M h => by omega))
  refine (pr_matrix_rank _).trans ?_
  apply bp_le
  simp only [num,Fintype.card_fin]
  let r := n/5
  have h1 : 5*r≤n := by unfold r; omega
  have h2 : n≤2*m+1 := by omega
  have h3 : 45≤m := by omega
  have hi : (m+m)*r+n≤m*m := by
    nlinarith only [h1,h2,h3,
      Nat.mul_le_mul_left m h1,Nat.mul_le_mul_left m h2,Nat.mul_le_mul_left m h3]
  have hh : ((m:ℝ)+m)*r+n ≤ m*(m:ℝ) := by exact_mod_cast hi
  unfold r at hh; linarith only [hh]

theorem pr_surj_rank {m} (hn : 100≤n) (hm : n/2≤m)
    (A : Draw p n →ₗ[F] Mat (Fin m) (Fin m))
    (h : Function.Surjective A) :
    pr unif (fun x => 5*(A x).rank < n) ≤ bp (- (n:ℝ)) := by
  classical
  have he := mapW_pr unif A (fun x => 5*x.rank<n)
  rw [map_unif_surjective A h] at he
  exact he.symm.le.trans (rank_fifth_bound m n hm hn)

theorem ztest_prob (p : Shape) (s t : Label p.b) (hj : 1≤p.j)
    (c : Vec (MBits p)) (b : Vec Bool) (hn : 100≤n) :
    pr unif (fun x : Draw p n => s ≠ t ∧ c≠0 ∧
      5*blockRank Block.Z s t (indexedSum (drawn x) c+selfSum (drawn x) b)<n)
      ≤ bp (- (n:ℝ)) := by
  classical
  by_cases h : s≠t ∧ c≠0
  · simp only [← and_assoc (a:=s≠t),blockRank,map_add,obsZ_self,add_zero]
    refine le_trans (pr_mono unif_law.nz ?_) (pr_surj_rank hn (by omega) (obsZ p n s t c) (obsZ_surj _ _ hj h.1 h.2))
    exact fun x hx => hx.2
  simp_rw [← and_assoc (a:=s≠t),h,false_and,pr_false]
  exact (bp_pos _).le

theorem stest_prob (p : Shape) (s t : Label p.b) (hj : 1≤p.j)
    (b : Vec Bool) (hn : 100≤n) :
    pr unif (fun x : Draw p n => s ≠ t ∧ b≠0 ∧
      5*blockRank Block.sharp s t (selfSum (drawn x) b)<n)
      ≤ bp (- (n:ℝ)) := by
  classical
  by_cases h : s≠t ∧ b≠0
  · simp only [← and_assoc (a:=s≠t),blockRank,pull_selfPart _ _ hj]
    let l := Fin.castLE (show n/2≤n by omega)
    let r (i : Fin (n/2)) : Fin n := ⟨n/2+i.val,by have := i.isLt; omega⟩
    have he : Function.Surjective (obsHalf p s t b n l r) := by
      refine obsHalf_surj _ _ h.1 h.2 _ (Fin.castLE_injective _) (fun i j h => ?_) ?_
      · exact Fin.ext (Nat.add_left_cancel (congrArg Fin.val h))
      intro i j h
      have he : i.val = n/2+j.val := congrArg Fin.val h
      have hg := i.isLt; omega
    apply le_trans _ (pr_surj_rank hn (by omega) (obsHalf p s t b n l r) he)
    refine pr_mono unif_law.nz fun x hx => lt_of_le_of_lt ?_ hx.2
    exact Nat.mul_le_mul_left _ ((selfPartial (p:=p) s t b x).rank_submatrix_le l r)
  simp_rw [← and_assoc (a:=s≠t),h,false_and,pr_false]
  exact (bp_pos _).le

theorem binary_likely (p : Shape) (hj : 1≤p.j) :
    ∀ᶠ n : ℕ in atTop,
      pr unif (fun x : Draw p n => ¬binaryGood (drawn x)) < 1/4 := by
  classical
  let I := Label p.b × Label p.b × Vec (MBits p) × Vec Bool
  let J := Label p.b × Label p.b × Vec Bool
  let T := I⊕J
  let m := num T
  have h : Tendsto (fun n:ℕ=>m*bp (- (n:ℝ))) atTop (𝓝 0) := by
    have h : Tendsto (fun n:ℕ=>bp (-(1:ℝ)*(n:ℝ))) atTop (𝓝 0) :=
      (bp_tendsto_zero zero_lt_one).comp tendsto_natCast_atTop_atTop
    simpa using h.const_mul m
  filter_upwards [h.eventually (gt_mem_nhds (show (0:ℝ)<1/4 by norm_num)),
    eventually_ge_atTop 100] with n hn hg
  let bad (i : T) (x : Draw p n) :=
    match i with
    | .inl (s,t,c,b) => s≠t ∧ c≠0 ∧ 5*blockRank Block.Z s t
        (indexedSum (drawn x) c+selfSum (drawn x) b)<n
    | .inr (s,t,b) => s≠t ∧ b≠0 ∧ 5*blockRank Block.sharp s t (selfSum (drawn x) b)<n
  have he (i : T) : pr unif (bad i) ≤ bp (- (n:ℝ)) := by
    rcases i with ⟨s,t,c,b⟩|⟨s,t,b⟩
    · exact ztest_prob _ _ _ hj _ _ hg
    exact stest_prob _ _ _ hj _ hg
  have hi : pr unif (fun x => ∃ i, bad i x) ≤ m*bp (- (n:ℝ)) :=
    (pr_exists_le unif_law.nz bad).trans ((Finset.sum_le_sum (fun i _ => he i)).trans_eq (by
      rw [Finset.sum_const, Finset.card_univ,nsmul_eq_mul]))
  apply lt_of_le_of_lt (le_trans (pr_mono unif_law.nz ?_) hi) hn
  intro x hx
  by_contra! H
  apply hx
  intro s t hst
  constructor
  · intro c b hc
    exact le_of_not_gt fun e => H (Sum.inl (s,t,c,b)) ⟨hst,hc,e⟩
  intro b hb
  exact le_of_not_gt fun e => H (Sum.inr (s,t,b)) ⟨hst,hb,e⟩
end HadwigerCounterexample

end

end OAI
