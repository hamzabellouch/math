import Mathlib

namespace OAI

namespace SharpRamseyFive.Marking
open scoped BigOperators Classical

lemma log_contraction_drop (x y δ : ℝ) (hx : 1≤x) (hy : 0≤y) (hδ : 0≤δ)
    (hc : y≤(1-δ)*x) : Real.log (1+y)≤Real.log (1+x)-δ/2 := by
  have hx0 : 0<1+x := by linarith
  have hy0 : 0<1+y := by linarith
  have hh := Real.log_le_sub_one_of_pos (div_pos hy0 hx0)
  rw [Real.log_div hy0.ne' hx0.ne'] at hh
  have hd : (1+y)/(1+x)-1≤ -δ/2 := by
    have hrat : (1+y)/(1+x)≤1-δ/2 := by
      apply (div_le_iff₀ hx0).mpr
      nlinarith [mul_nonneg hδ (show 0≤x-1 by linarith)]
    linarith
  linarith

lemma telescoping_drop (f : ℕ → ℝ) (e : ℕ → ℝ) (N : ℕ)
    (hstep : ∀ i<N,f (i+1)≤f i-e i) :
    f N≤f 0-∑ i∈Finset.range N,e i := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hi := ih (fun i hi => hstep i (Nat.lt_succ_of_lt hi))
    have hh := hstep N (Nat.lt_succ_self N)
    rw [Finset.sum_range_succ]
    linarith

theorem finite_scan_bound {Y : Type*} [DecidableEq Y]
    (S : ℕ → Fin 5 → Finset Y) (chosen : ℕ → Option (Fin 5))
    (N : ℕ) (δ : ℝ) (hδ : 0<δ)
    (hmono : ∀ i<N,∀ j,S (i+1) j⊆S i j)
    (hchosen : ∀ i<N,∀ j,chosen i=some j →
      (S i j).Nonempty ∧ ((S (i+1) j).card:ℝ)≤(1-δ)*(S i j).card) :
    (((Finset.range N).filter fun i => (chosen i).isSome).card:ℝ)*(δ/2)≤
      ∑ j:Fin 5,Real.log (1+(S 0 j).card) := by
  let Φ : ℕ → ℝ:=fun i => ∑ j:Fin 5,Real.log (1+(S i j).card)
  let e : ℕ → ℝ:=fun i => if (chosen i).isSome then δ/2 else 0
  have hd : ∀ i<N,Φ (i+1)≤Φ i-e i := by
    intro i hi
    have hj (j : Fin 5) : Real.log (1+(S (i+1) j).card)≤Real.log (1+(S i j).card) := by
      apply Real.log_le_log (by positivity)
      have hh : ((S (i+1) j).card:ℝ)≤(S i j).card := by exact_mod_cast Finset.card_le_card (hmono i hi j)
      linarith
    cases hc : chosen i with
    | none =>
      simp only [e,hc,Option.isSome_none,Bool.false_eq_true,ite_false,sub_zero]
      exact Finset.sum_le_sum fun j _ => hj j
    | some j =>
      have hcol:=hchosen i hi j hc
      have hx : (1:ℝ)≤(S i j).card := by exact_mod_cast Finset.card_pos.mpr hcol.1
      have hdrop:=log_contraction_drop (S i j).card (S (i+1) j).card δ hx (by positivity) hδ.le hcol.2
      have hs : (∑ k:Fin 5,Real.log (1+(S (i+1) k).card))≤
          ∑ k:Fin 5,(Real.log (1+(S i k).card)-(if k=j then δ/2 else 0)) := by
        apply Finset.sum_le_sum
        intro k _
        by_cases hk : k=j
        · subst k; simpa using hdrop
        · simpa only [ite_eq_right hk,sub_zero] using hj k
      simpa [Φ,e,hc,Finset.sum_sub_distrib] using hs
  have hf:=telescoping_drop Φ e N hd
  have hnonneg : 0≤Φ N := Finset.sum_nonneg fun j _ => Real.log_nonneg (by
    have h : (0:ℝ)≤(S N j).card := by positivity
    linarith)
  have he : (∑ i∈Finset.range N,e i)=
      (((Finset.range N).filter fun i => (chosen i).isSome).card:ℝ)*(δ/2) := by
    simp only [e,←Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
  rw [he] at hf
  change _≤Φ 0
  linarith

end SharpRamseyFive.Marking

end OAI
