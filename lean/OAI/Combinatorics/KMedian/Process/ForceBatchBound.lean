import Mathlib
import OAI.Combinatorics.KMedian.Probability.FiniteLaws
import OAI.Combinatorics.KMedian.Geometry.PotentialBounds
import OAI.Combinatorics.KMedian.Geometry.FixedBatchTransition
import OAI.Combinatorics.KMedian.Geometry.TimeAdvance

namespace OAI

section
section
namespace MetricKMedian.PhysicalPotential
open Analytic
variable {I : Type*}

theorem time_increase_le {x g h b : ℝ} {d : I → ℝ} {S : Finset I}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hg : 0 ≤ g) (hh : 0 ≤ h)
    (hd0 : ∀ i ∈ S, 0 ≤ d i) (hy : mass g S ≤ 1) :
    potential (x*Real.exp (-h)) g d S b-potential x g d S b ≤
      (2*h+6*h^2)*cost g d S := by
  have he := potential_time_error (b := b) hx0 hx1 hg hd0 hy hh
  have hr := (abs_le.mp (abs_timeRate hx0 hx1 (mass_nonneg hg S) hy)).2
  have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr hh) (cost_nonneg hg hd0)
  have ht := (le_abs_self _).trans he
  nlinarith only [ht, hm]

end MetricKMedian.PhysicalPotential

namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential Analytic
variable {I E : Type*} [DecidableEq I] [DecidableEq E] [Fintype E]

noncomputable def nextAliveAt (D : Actions I E) (a : ℝ) (d : I → ℝ)
    (S : Finset I) (A : Finset E) : Finset I :=
  if h : (internal D S A).Nonempty then
    retained a (d (D.source h.choose)) d (physical D S A)
  else physical D S A

 theorem nextAliveAt_subset (D : Actions I E) (a : ℝ) (d : I → ℝ)
    (S : Finset I) (A : Finset E) : nextAliveAt D a d S A ⊆ S := by
  unfold nextAliveAt
  split_ifs
  · exact (retained_subset _ _ _ _).trans (physical_subset D S A)
  · exact physical_subset D S A

 theorem nextAliveAt_zero (D : Actions I E) (a : ℝ) (d : I → ℝ)
    (S : Finset I) (A : Finset E) (ha : A ∩ relevant D S=∅) :
    nextAliveAt D a d S A=S := by
  have hi : internal D S A=∅ := by simp only [internal, ha, filter_empty]
  simp only [nextAliveAt, hi, Finset.not_nonempty_empty, dite_false]
  rw [physical_restrict, ha]
  simp only [physical, biUnion_empty, sdiff_empty]

 theorem changeAt_probability_le (D : Actions I E) (μ : FiniteLaw (Finset E))
    (a : ℝ) (d : I → ℝ) (S : Finset I) {Q : ℝ}
    (hmarg : ∀ e ∈ relevant D S, μ.prob (fun A => e ∈ A) ≤ Q) :
    μ.prob (fun A => nextAliveAt D a d S A ≠ S) ≤ ((relevant D S).card:ℝ)*Q := by
  have hm := μ.prob_mono (E := fun A => nextAliveAt D a d S A ≠ S)
    (F := fun A => ∃ e ∈ relevant D S, e ∈ A) (by
      intro A ha
      by_contra hn
      have hi : A ∩ relevant D S=∅ := eq_empty_iff_forall_notMem.mpr (by
        intro e he
        exact hn ⟨e, (mem_inter.mp he).2, (mem_inter.mp he).1⟩)
      exact ha (nextAliveAt_zero D a d S A hi))
  have hu := μ.prob_exists_le_sum (relevant D S) (fun e A => e ∈ A)
  have hs := sum_le_sum hmarg
  simp only [sum_const, nsmul_eq_mul] at hs
  exact hm.trans (hu.trans hs)

theorem post_force_bound (D : Actions I E) (μ : FiniteLaw (Finset E))
    {x g h b V : ℝ} (a : ℝ) (d : I → ℝ) (S : Finset I)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hg0 : 0 < g) (hg1 : g ≤ 1)
    (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hV : 0 ≤ V)
    (hd0 : ∀ i ∈ S, 0 ≤ d i) (hy : mass g S ≤ 1)
    (hVS : PhysicalPotential.cost g d S ≤ V) (hb0 : 0 ≤ b) (hbV : b ≤ V/g)
    (hcap : ∀ A, 0 ≤ nextCap D d b A)
    (hmarg : ∀ e ∈ relevant D S, μ.prob (fun A => e ∈ A) ≤ 2*h*g) :
    μ.expect (fun A => potential (x*Real.exp (-h)) g d (nextAliveAt D a d S A)
      (nextCap D d b A)-potential x g d S b) ≤
      (8*((relevant D S).card:ℝ)+8)*h*V := by
  let K : ℝ := (3+1/g)*V
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hpot0 : 0 ≤ potential x g d S b := by
    rw [potential, ← coefficient_eq]
    have ha := coefficient_ge_one (x := x) (mass_nonneg hg0.le S)
    exact add_nonneg (mul_nonneg (by linarith only [ha]) (cost_nonneg hg0.le hd0))
      (mul_nonneg (sub_nonneg.mpr hy) hb0)
  have hf : μ.expect (fun A => potential x g d (nextAliveAt D a d S A)
      (nextCap D d b A)-potential x g d S b) ≤
      K*μ.prob (fun A => nextAliveAt D a d S A ≠ S) := by
    rw [FiniteLaw.prob, ← μ.expect_mul]
    apply μ.expect_mono
    intro A
    have hsub := nextAliveAt_subset D a d S A
    have hnewV := (cost_mono hg0.le hd0 hsub).trans hVS
    have hy' := (mass_mono hg0.le hsub).trans hy
    by_cases heq : nextAliveAt D a d S A=S
    · simp only [heq, ne_eq, not_true_eq_false, ite_false, mul_zero]
      have he := mul_le_mul_of_nonneg_left (nextCap_le_force D d b A) (sub_nonneg.mpr hy)
      unfold potential
      linarith only [he]
    · simp only [heq, ne_eq, not_false_eq_true, ite_true, mul_one]
      have hcoeff := (coefficient_bounds hx0 hx1 (mass_nonneg hg0.le _) hy').2
      have hprod := mul_le_mul hcoeff hnewV
        (cost_nonneg hg0.le (fun i hi => hd0 i (hsub hi))) (by norm_num : (0:ℝ) ≤ 3)
      have hcapV := (nextCap_le_force D d b A).trans hbV
      have hcap' := mul_le_mul_of_nonneg_right
        (show 1-mass g (nextAliveAt D a d S A) ≤ 1 by
          linarith only [mass_nonneg hg0.le (nextAliveAt D a d S A)]) (hcap A)
      rw [potential, ← coefficient_eq]
      dsimp only [K]
      simp only [div_eq_mul_inv, one_mul] at hcapV ⊢
      nlinarith only [hprod, hcapV, hcap', hpot0]
  have hp := changeAt_probability_le D μ a d S hmarg
  have hf' := hf.trans (mul_le_mul_of_nonneg_left hp hK)
  have ht : μ.expect (fun A => potential (x*Real.exp (-h)) g d (nextAliveAt D a d S A)
      (nextCap D d b A)-potential x g d (nextAliveAt D a d S A) (nextCap D d b A)) ≤
      (2*h+6*h^2)*V := by
    apply (μ.expect_mono (fun A => ?_)).trans_eq (μ.expect_const _)
    have hsub := nextAliveAt_subset D a d S A
    exact (time_increase_le hx0 hx1 hg0.le hh0 (fun i hi => hd0 i (hsub hi))
      ((mass_mono hg0.le hsub).trans hy)).trans
      (mul_le_mul_of_nonneg_left ((cost_mono hg0.le hd0 hsub).trans hVS) (by positivity))
  have he : (fun A => potential (x*Real.exp (-h)) g d (nextAliveAt D a d S A)
      (nextCap D d b A)-potential x g d S b)=
      (fun A => (potential x g d (nextAliveAt D a d S A) (nextCap D d b A)-potential x g d S b)+
        (potential (x*Real.exp (-h)) g d (nextAliveAt D a d S A) (nextCap D d b A)-
          potential x g d (nextAliveAt D a d S A) (nextCap D d b A))) := by
    funext A; ring
  rw [he, μ.expect_add]
  apply (add_le_add hf' ht).trans
  have hk : K*(((relevant D S).card:ℝ)*(2*h*g)) ≤
      8*((relevant D S).card:ℝ)*h*V := by
    have hid : K*(((relevant D S).card:ℝ)*(2*h*g))=
        (6*g+2)*(((relevant D S).card:ℝ)*h*V) := by
      dsimp only [K]
      field_simp
      ring
    rw [hid]
    have hg' : 6*g+2 ≤ 8 := by linarith only [hg1]
    calc
      _ ≤ 8*(((relevant D S).card:ℝ)*h*V) := mul_le_mul_of_nonneg_right hg' (by positivity)
      _ = _ := by ring
  have ht' : (2*h+6*h^2)*V ≤ 8*h*V := by
    apply mul_le_mul_of_nonneg_right _ hV
    nlinarith only [mul_nonneg hh0 (sub_nonneg.mpr hh1)]
  nlinarith only [hk, ht']

end MetricKMedian.FixedBatch
end
end

end OAI
