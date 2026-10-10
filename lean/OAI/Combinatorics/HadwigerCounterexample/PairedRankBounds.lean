import OAI.Combinatorics.HadwigerCounterexample.EndpointGramRanks

namespace OAI

/-! # Paired Rank Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Finset LinearMap Module Matrix Function
open scoped BigOperators
variable {I J : Type} [Fintype I] [Fintype J] {n N : ℕ}

theorem rank_jump_prob (n d N : ℕ) :
    pr unif (fun q : PlusRack (Fin n) N× PlusRack (Fin n) N => rankJump q.1 q.2 d) ≤
      bp ((2*n-(N:ℝ))*d) := by
  classical
  let V := PlusRack (Fin n) N
  let e : V×V ≃ PlusRack (Fin n⊕Fin n) N := {
    toFun q := fromCols q.1 q.2
    invFun M := (M.submatrix _root_.id Sum.inl,M.submatrix _root_.id Sum.inr)
    left_inv x := rfl
    right_inv x := by ext i j; cases j <;> rfl }
  have ht := pr_deficient (I:=Fin N) (J:=Fin n⊕Fin n) d
  rw [←unif_equiv e,mapW_pr] at ht
  simp only [num,Fintype.card_fin,Fintype.card_sum,←two_mul,Nat.cast_mul,Nat.cast_ofNat] at ht; exact ht

set_option maxHeartbeats 800000 in
theorem paired_rank_norm (n d r N : ℕ) (hN : 2*(n:ℝ)-N≤ -1)
    (G H W : Mat (Fin n) (Fin n)) (v : F) :
    pr (pairW (unifOn (gramGood G)) (unifOn (gramGood H)))
      (fun s => (crossSquare n N W v s).rank ≤ r) ≤
        16*(bp ((2*n-(N:ℝ))*d)+bp ((2*n:ℝ)*r-(n-d:ℝ)*n)) := by
  classical
  let A := PlusRack (Fin n) N
  let P (s : (A×A)×A×A) := gramGood G s.1∧gramGood H s.2
  let Q (s : (A×A)×A×A) := (crossSquare n N W v s).rank≤r
  let p := bp (-(n:ℝ)*n); let c := bp ((2*n:ℝ)*r-(n-d:ℝ)*n)
  let b := bp ((2*n-(N:ℝ))*d)
  have hp : 0<p := bp_pos _; have hb : 0≤b := (bp_pos _).le; have hc : 0≤c := (bp_pos _).le
  have hP :
      (p/4)^2 ≤ pr unif P := by
    have he (G) : p/4 ≤ pr unif (fun i : A×A => gramGood G i) := by
      have hh : num (Fin n)+num (Fin n)-num (Fin N) ≤ -1 := by
        simp only [num,Fintype.card_fin]; linarith only [hN]
      simpa only [p,num,Fintype.card_fin] using gram_norm_quarter G hh
    unfold P; rw [pair_unif,pairW_pr,pow_two]
    exact mul_le_mul (he _) (he _) (by positivity) (pr_nonneg unif_law.nz)
  have he (x y : A) :
      pr unif (fun s : A×A=>P ((x,s.1),(y,s.2))∧Q ((x,s.1),(y,s.2))) ≤
        p^2 * (ind (rankJump x y d)+c) := by
    rw [pair_unif]
    have h0 : 0 ≤ p^2*(ind (rankJump x y d)+c) := mul_nonneg (sq_nonneg _) (add_nonneg
      (ind_nonneg _) hc)
    by_cases hx : Injective x.mulVec ∧ Injective y.mulVec
    · have hh := shift_square n N r d x y G H W v hx.1 hx.2
      exact (pr_mono (pairW_law unif_law unif_law).nz fun i h =>
        ⟨⟨h.1.1.1,h.1.2.1⟩,h.2⟩).trans hh
    exact le_trans (le_of_eq ((congrArg (pr (pairW _ _)) (show
        (fun s : A×A=>P ((x,s.1),(y,s.2))∧Q ((x,s.1),(y,s.2)))=(fun s=>False) from
        funext fun i => propext ⟨fun h => hx ⟨h.1.1.2.1,h.1.2.2.1⟩,False.elim⟩)).trans
        (pr_false _))) h0
  have ht : pr unif (fun s => P s∧Q s)≤p^2*(b+c) := by
    let f : ((A×A)×A×A)≃ ((A×A)×A×A) := {
      toFun x := ((x.1.1,x.2.1),(x.1.2,x.2.2))
      invFun x := ((x.1.1,x.2.1),(x.1.2,x.2.2))
      left_inv _ := rfl
      right_inv _ := rfl }
    rw [←unif_equiv f,mapW_pr,pair_unif,pr,pairW_avg]
    refine (avg_mono (unif_law (α:=A×A)).nz (fun x => he x.1 x.2)).trans ?_
    rw [avg_mul',avg_add,unif_law.avg_const]
    exact mul_le_mul_of_nonneg_left (add_le_add_left (rank_jump_prob n d N) c) (sq_nonneg _)
  rw [←unifOn_and_prod,←on_unif,pr_on]
  refine (div_le_div₀ (mul_nonneg (sq_nonneg _) (add_nonneg hb hc)) ht
    (show 0 < (p/4)^2 from by positivity) hP).trans_eq ?_
  change p^2*(b+c) / ((p/4)^2)=16*(b+c)
  field_simp; ring

open Filter
theorem paired_rank_scale :
    ∀ᶠ n : ℕ in atTop,∀ N : ℕ, 4*n≤ N →
    ∀ (G H W : Mat (Fin n) (Fin n)) (v : F),
    pr (pairW (unifOn (gramGood G)) (unifOn (gramGood H)))
      (fun s => 5*(crossSquare n N W v s).rank < n) ≤ bp (-(n:ℝ)*n/4) := by
  filter_upwards [eventually_ge_atTop 100] with n hn N hN G H W v
  let d := n/4; let r := n/5
  have hn' : (100:ℝ) ≤ n := by exact_mod_cast hn
  have hN' : 4*(n:ℝ)≤N := by exact_mod_cast hN
  have hr : 5*(r:ℝ)≤n := by exact_mod_cast (show 5*r ≤ n by unfold r; omega)
  have hd : 4*(d:ℝ)≤n := by exact_mod_cast (show 4*d≤n by unfold d; omega)
  have hd' : (n:ℝ)≤4*d+3 := by exact_mod_cast (show n ≤ 4*d+3 by unfold d; omega)
  have hh := paired_rank_norm n d r N (by linarith only [hN',hn']) G H W v
  let z := (-(n:ℝ)*n/4-5)
  have hg : 32*bp z=bp (-(n:ℝ)*n/4) := by
    have he : bp 5=32 := by norm_num [bp]
    rw [←he,←bp_add]; unfold z; ring_nf
  rw [←hg]
  refine (pr_mono (subLaw_pair (unifOn_sub _) (unifOn_sub _)).nz fun i hi =>
    (by unfold r; omega : (crossSquare n N W v i).rank ≤ r)).trans (hh.trans ?_)
  have hq : bp ((2*n-(N:ℝ))*d)≤bp z := by
    apply bp_le
    unfold z
    nlinarith only [mul_le_mul_of_nonneg_right hN' (Nat.cast_nonneg d : 0≤(d:ℝ)),
      mul_le_mul_of_nonneg_right hn' (Nat.cast_nonneg n : 0≤(n:ℝ)),hn',
      mul_le_mul_of_nonneg_right hd' (Nat.cast_nonneg n : 0≤(n:ℝ))]
  have hm : bp ((2*n:ℝ)*r-(n-d:ℝ)*n)≤bp z := by
    apply bp_le; unfold z
    nlinarith only [mul_le_mul_of_nonneg_right hr (Nat.cast_nonneg n : 0≤(n:ℝ)),
      mul_le_mul_of_nonneg_right hn' (Nat.cast_nonneg n : 0≤(n:ℝ)),hn',
      mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg n : 0≤(n:ℝ))]
  linarith only [hq,hm]
end HadwigerCounterexample

end

end OAI
