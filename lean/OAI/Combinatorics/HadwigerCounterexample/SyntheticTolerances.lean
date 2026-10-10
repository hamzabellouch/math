import OAI.Combinatorics.HadwigerCounterexample.GramArrayConcentration

namespace OAI

/-! # Synthetic Tolerances -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Function Filter Real
open scoped BigOperators Topology
variable {p : Shape} {I : Type} [Fintype I] [DecidableEq I] {n N : ℕ}

theorem magazine_calendar (p : Shape) (I : Type) [Fintype I] [DecidableEq I]
    (M : ℕ) (hM : 1≤M) (hj : 1≤p.j) (L ε : ℝ) (hL : 0≤L) (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, let N:=M*n; ∀ l s f, ∀ m : Mixer p n,2*num (Full p n)<N →
      ∀ P : Display p I N→Prop, ∀ a : I→Tickets p, ∀ w : Wgt (Orient p n N),
      IsLaw w → (∀ i,w i≤L*raw m N i) →
      (∀ i,w i≠0 → magazine p l s f P a i ≤ ε/2) →
      pr (displayLaw p I N (labGram p l f a)) P ≤ ε := by
  classical
  let g:= tied (drStage p I) Bool
  let k:=num I+num (Bool × Comp p.g × I)
  let C n := 2*netFact g*twinkle g k (M*n) + bp (num Bool*num I-(n:ℕ))
  have ht : Tendsto (fun n=>L*C n) atTop (𝓝 0) := by
    have hh {N:ℕ→ℝ} (h : Tendsto N atTop atTop) (i : ℝ) (b : ℝ) (hb : 0<b) :
        Tendsto (fun n => bp (i-b*N n)) atTop (𝓝 0) := by
      simp_rw [sub_eq_add_neg,bp_add,←neg_mul]
      simpa using ((bp_tendsto_zero hb).comp h).const_mul (bp i)
    have hN := cast_tops M hM
    have h1 := (hh hN k 1 (by norm_num))
    have h2 : Tendsto (fun n:ℕ => bp (-(↑(M*n):ℝ)/2)) atTop (𝓝 0) := by
      refine (tendsto_congr' ?_).mp (hh hN 0 (1/2) (by norm_num))
      exact .of_forall (fun x => by ring_nf)
    have h3 := hh (tendsto_natCast_atTop_atTop (R:=ℝ)) (num Bool*num I) 1 (by norm_num)
    have hv := (((((h1.const_mul 2).const_mul (num (Comp p.g))).add h2).const_mul
      (2*netFact g)).add h3).const_mul L
    simpa only [C,twinkle,mul_zero,zero_add,add_zero,one_mul] using hv
  let b:= ε/2
  have hb : 0<b := by positivity
  filter_upwards [ht.eventually (gt_mem_nhds (show 0<b^2 by positivity)),
    (cast_tops M hM).eventually (eventually_ge_atTop (2*k+1)),eventually_ge_atTop (2*p.r)]
    with n hn hq hU N l s f m hN P a w hw he h
  change 2*k+1 ≤ (N:ℝ) at hq
  have ha : num I ≤ k := le_add_of_nonneg_right (Nat.cast_nonneg _)
  have hk : num (Bool × Comp p.g × I)≤ k := le_add_of_nonneg_left (Nat.cast_nonneg _)
  let u := magazine p l s f P a (n:=n); let F:= pr (displayLaw p I N (labGram p l f a)) P
  let X i := (u i-F)^2
  have hh :
      avg (raw m N) X ≤ C n := magazine_var p l s f P a m hN hj hU (by linarith only [ha,hq])
        k hk (by linarith only [hq])
  by_contra! hl
  change ε<F at hl
  have hB : b^2 ≤ avg w X := by
    rw [← hw.avg_const (b^2)]; unfold avg
    apply Finset.sum_le_sum; intro i _
    by_cases he : w i=0
    · rw [he]; simp
    apply mul_le_mul_of_nonneg_left _ (hw.nz _)
    have hp : u i ≤ b := h i he
    change b^2≤ (u i-F)^2
    unfold b at *
    nlinarith only [hp,hε,hl]
  have hX : avg w X ≤ L*C n := by
    refine (avg_mono_left (fun i=>sq_nonneg (u i - F)) he).trans ?_
    apply le_trans ?_ (mul_le_mul_of_nonneg_left hh hL)
    simp only [X,avg,mul_assoc,Finset.mul_sum]
    exact le_rfl
  exact not_lt_of_ge (hB.trans hX) hn
end HadwigerCounterexample

end

end OAI
