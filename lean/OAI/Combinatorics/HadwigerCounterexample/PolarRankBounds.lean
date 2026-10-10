import OAI.Combinatorics.HadwigerCounterexample.MixerProductVariables

namespace OAI

/-! # Polar Rank Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Matrix
open scoped BigOperators

variable {I J U : Type} [Fintype I] [Fintype J]

def swapM (I : Type) [DecidableEq I] : Mat (I⊕I) (I⊕I) :=
  fromBlocks (0:Mat I I) (1:Mat I I) (1:Mat I I) 0

theorem swapM_rank [DecidableEq I] :
    (swapM I).rank = Fintype.card (I⊕I) := by
  have h : swapM I * swapM I = 1 := by simp [swapM, fromBlocks_multiply]
  apply mrk_inj.mp
  intro x y hxy
  have he (x) : swapM I *ᵥ (swapM I *ᵥ x)=x := by rw [mulVec_mulVec, h, Matrix.one_mulVec]
  change swapM I*ᵥx=swapM I*ᵥy at hxy
  rw [← he x,hxy,he]

theorem alt_of_forms [Fintype U] [DecidableEq J] (P Q : Mat I J) (W : Mat I U) :
    pullM W W (P*Qᵀ + (P*Qᵀ)ᵀ) =
      liftM (Wᵀ * fromCols P Q) (Wᵀ * fromCols P Q) (swapM J) := by
  have hh : P*Qᵀ+(P*Qᵀ)ᵀ = liftM (fromCols P Q) (fromCols P Q) (swapM J) := by
    simp only [liftM_def,swapM,fromCols_mul_fromBlocks,
      Matrix.mul_one,Matrix.mul_zero,add_zero,transpose_fromCols,
      fromCols_mul_fromRows, transpose_mul,transpose_transpose,add_comm]
  rw [hh]
  apply liftM_comp

variable {p : Shape} {n : ℕ}

theorem flarge {r : Comp p.g→ℕ} (P Q : Parts p n r) :
    ∃ S : Space (Ray p n), (∀ i,colSp (P i) ≤ S ∧ colSp (Q i) ≤ S) ∧
      dim S ≤ 2*(∑ i, r i) := by
  classical
  have he (J : Finset (Comp p.g)) :
      ∃ S : Space (Ray p n), (∀ i∈J,colSp (P i) ≤ S ∧ colSp (Q i) ≤ S) ∧
        dim S ≤ 2*∑ i∈J,r i := by
    induction J using Finset.induction with
    | empty => exact ⟨⊥,fun _ h => (Finset.notMem_empty _ h).elim,
        (finrank_bot _ _).le.trans (Nat.zero_le _)⟩
    | insert i J hi ih =>
      obtain ⟨S,hS,h⟩ := ih
      let T := colSp (P i) ⊔ colSp (Q i)
      refine ⟨S⊔T,fun j hj => ?_, ?_⟩
      · rcases Finset.mem_insert.mp hj with rfl|hj
        · exact ⟨le_trans (show colSp _ ≤ T from le_sup_left) le_sup_right,
            le_trans (show colSp _ ≤ T from le_sup_right) le_sup_right⟩
        · exact ⟨(hS j hj).1.trans le_sup_left,(hS j hj).2.trans le_sup_left⟩
      have hh : dim T ≤ 2*r i := by
        have hp (P : Parts p n r) : dim (colSp (P i)) ≤ r i := by
          rw [colSp_dim]
          exact (Matrix.rank_le_card_width (P i)).trans_eq (Fintype.card_fin _)
        rw [two_mul]
        exact (Submodule.finrank_add_le_finrank_add_finrank ..).trans (Nat.add_le_add (hp _) (hp _))
      rw [Finset.sum_insert hi]
      apply le_trans (Submodule.finrank_add_le_finrank_add_finrank ..)
      exact (Nat.add_le_add h hh).trans (by omega)
  obtain ⟨S,h,g⟩ := he Finset.univ
  exact ⟨S,fun i => h _ (Finset.mem_univ i),g⟩

def urBad (K s0 : ℕ) (x : Profile p n) (l : Tag p.g) (s : Label p.b) (d : Draw p n) :=
  totalRank x ≤ K ∧ totalRank x>0 ∧ blockRank Block.Z s s
    (qmix (drawn d) x l+(qmix (drawn d) x l)ᵀ)<2*(p.J-s0)

def prodBound (p : Shape) (K : ℕ) := 4*p.J*(p.g-1)*K

theorem urBad_cap (K s0 : ℕ) (hg : 2≤p.g) (hj : s0≤p.J)
    (x : Profile p n) (l : Tag p.g) (s : Label p.b) :
    pr unif (urBad K s0 x l s) ≤
      bp (((prodBound p K : ℝ)+2*K-n)*(s0+1)) := by
  classical
  by_cases h : totalRank x≤K ∧ totalRank x>0
  swap
  · rw [show urBad K s0 x l s = fun _ => False by
      funext d; exact propext ⟨fun g => h ⟨g.1,g.2.1⟩,False.elim⟩,pr_false]
    exact (bp_pos _).le
  let R := blockRay p n s Block.Z
  let r i := (x i).rank
  obtain ⟨P,Q,h1,h2,h3⟩ :
      ∃ (P Q : Parts p n r), (∀ i,Function.Injective (P i).mulVec) ∧
        (∀ i,Function.Injective (Q i).mulVec) ∧ (∀ i,x i=P i*(Q i)ᵀ) := by
    choose A B h1 h2 h3 using fun i => rank_product (x i)
    refine ⟨A,fun i => (B i)ᵀ,h1,fun i => ?_,fun i => (h3 i).symm⟩
    rw [← transpose_surj_iff]; exact h2 i
  obtain ⟨S,hS,hrS⟩ := flarge P Q
  obtain ⟨T,hT,hv⟩ := choose_free (blockRay_inj p n s Block.Z) S
  let W := R*pack T
  let V := (Terms p l r)
  let A := stackL P Q l W
  have hb : Function.Surjective A := by
    apply stack_surj _ _ _ _
      (inj_comp_mat _ _ (blockRay_inj p n s Block.Z) (pack_inj T)) h1 h2
    · exact fun i => hv.mono_left (hS i).1
    exact fun i => hv.mono_left (hS i).2
  have hc : Fintype.card (V⊕V)=prodBound p (totalRank x) := by
    simp only [Fintype.card_sum,Terms,Fintype.card_prod,
      Fintype.card_fin,Fintype.card_sigma,V,Fintype.card_bool,card_star]
    unfold prodBound totalRank r; ring
  have hcard : 2*p.J ≤ Fintype.card (V⊕V) := by
    have he : 1 ≤ p.g-1 := by omega
    have hx : 1 ≤ totalRank x := h.2
    rw [hc]; unfold prodBound
    nlinarith only [Nat.mul_le_mul_left (p.J*(p.g-1)) hx,
      Nat.mul_le_mul_left p.J he, Nat.zero_le p.J]
  let Y (M : Mat (Fin (dim T)) (V ⊕ V)) :=
    M.rank+(s0+1) ≤ Fintype.card (V⊕V)
  have he (d) (hh : urBad K s0 x l s d) : Y (A d) := by
    let B := qmix (drawn d) x l + (qmix (drawn d) x l)ᵀ
    have hineq := rank_ge_congr (swapM V) (A d)
    have hx : pullM W W B=liftM (A d) (A d) (swapM V) := by
      dsimp only [B]
      rw [qmix_eq P Q l d h3]
      exact alt_of_forms _ _ W
    rw [← hx, swapM_rank] at hineq
    have hp : (pullM W W B).rank ≤ (pullM R R B).rank := by
      calc _ = (pullM (pack T) (pack T) (pullM R R B)).rank := by
                 unfold W pullM
                 rw [liftM_comp, Matrix.transpose_mul]
           _ ≤ _ := rank_lift_le _ _ _
    have hh1 : (pullM R R B).rank < 2*(p.J-s0) := hh.2.2
    change _+_ ≤ _
    omega
  have hpr := pr_mono (w:=unif) unif_subLaw.nz he
  change pr unif (urBad K s0 x l s) ≤ pr unif (fun d => Y (A d)) at hpr
  rw [← mapW_pr unif A Y,map_unif_surjective _ hb] at hpr
  apply le_trans (hpr.trans (pr_deficient _))
  apply bp_le
  have hp : num (V ⊕ V) ≤ prodBound p K := by
    have he : Fintype.card (V⊕V) ≤ prodBound p K := by rw [hc]; unfold prodBound; gcongr; exact h.1
    exact_mod_cast he
  have hx : n ≤ num (Fin (dim T)) + 2*(K:ℝ) := by
    rw [Fintype.card_fin] at hT
    have he : n ≤ Fintype.card (Fin (dim T)) + 2*K := by
      rw [Fintype.card_fin]
      exact hT.trans (Nat.add_le_add_left (hrS.trans (Nat.mul_le_mul_left _ h.1)) _)
    exact_mod_cast he
  push_cast; apply mul_le_mul_of_nonneg_right _ (by positivity)
  linarith only [hp,hx]
end HadwigerCounterexample

end

end OAI
