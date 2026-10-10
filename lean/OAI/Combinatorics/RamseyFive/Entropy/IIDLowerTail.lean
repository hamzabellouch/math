import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.Hits

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
variable {A : Type*} [Fintype A]

lemma exp_neg_one_le_half : Real.exp (-1) ≤ (1/2:ℝ) := by
  have h := Real.add_one_le_exp (1:ℝ)
  rw [Real.exp_neg]
  rw [←one_div]
  exact (div_le_iff₀ (Real.exp_pos 1)).mpr (by linarith)

lemma expected_exp_neg_hit (p : Law A) (H : Finset A) :
    (∑a,p a*Real.exp (-(if a∈H then (1:ℝ) else 0)))=
      1-(1-Real.exp (-1))*eventMass p H := by
  have hh (a : A) : p a*Real.exp (-(if a∈H then (1:ℝ) else 0))=
      p a-(1-Real.exp (-1))*(if a∈H then p a else 0) := by
    split_ifs
    · ring
    · norm_num
  simp_rw [hh]
  rw [Finset.sum_sub_distrib,p.sum_one,←Finset.mul_sum]
  simp only [eventMass,←Finset.sum_filter,Finset.filter_univ_mem]

lemma expected_exp_neg_hits (p : Law A) (H : Finset A) (n : ℕ) :
    (∑x,iid p (Fin n) x*Real.exp (-hits H x))=
      (1-(1-Real.exp (-1))*eventMass p H)^n := by
  have hh (x : Fin n→A) : Real.exp (-hits H x)=
      ∏i,Real.exp (-(if x i∈H then (1:ℝ) else 0)) := by
    rw [hits,←Finset.sum_neg_distrib,Real.exp_sum]
  change (∑x,(∏i,p (x i))*Real.exp (-hits H x))=_
  simp_rw [hh,←Finset.prod_mul_distrib]
  rw [←Fintype.sum_pow (fun a=>p a*Real.exp (-(if a∈H then (1:ℝ) else 0))) n,
    expected_exp_neg_hit]

lemma expected_exp_neg_hits_le (p : Law A) (H : Finset A) (n : ℕ) :
    (∑x,iid p (Fin n) x*Real.exp (-hits H x)) ≤
      Real.exp (-eventMass p H*n/2) := by
  have hbase : 0 ≤ 1-(1-Real.exp (-1))*eventMass p H := by
    rw [←expected_exp_neg_hit]
    exact Finset.sum_nonneg fun a _=>mul_nonneg (p.nonneg a) (Real.exp_pos _).le
  have hp := eventMass_nonneg p H
  have hsmall : 1-(1-Real.exp (-1))*eventMass p H ≤ Real.exp (-eventMass p H/2) := by
    have he := Real.add_one_le_exp (-eventMass p H/2)
    have hh := mul_le_mul_of_nonneg_right exp_neg_one_le_half hp
    nlinarith
  rw [expected_exp_neg_hits]
  calc
    _ ≤ (Real.exp (-eventMass p H/2))^n := pow_le_pow_left₀ hbase hsmall n
    _ = _ := by rw [←Real.exp_nat_mul];congr 1;ring

theorem iid_low_hit_event (p : Law A) (H : Finset A) (n : ℕ) (t : ℝ)
    (E : Finset (Fin n→A)) (hE : ∀x∈E,hits H x ≤ t) :
    eventMass (iid p (Fin n)) E ≤ Real.exp (t-eventMass p H*n/2) := by
  have hx := event_markov (iid p (Fin n)) (fun x=>Real.exp (-hits H x))
    (fun x=>(Real.exp_pos _).le) (Real.exp (-t)) E (fun x hx=>
      Real.exp_le_exp.mpr (neg_le_neg (hE x hx)))
  have hh := hx.trans (expected_exp_neg_hits_le p H n)
  calc
    _ ≤ Real.exp (-eventMass p H*n/2)/Real.exp (-t) :=
      (le_div_iff₀ (Real.exp_pos _)).mpr (by simpa [mul_comm] using hh)
    _ = _ := by rw [←Real.exp_sub];congr 1;ring

theorem iid_cap_tail (p : Law A) (H : Finset A) (n : ℕ) (q : ℝ) (hq : 0 < q)
    (hH : 1/(2*q) ≤ eventMass p H) :
    eventMass (iid p (Fin n)) (Finset.univ.filter fun x=>hits H x < (n:ℝ)/(5*q)) ≤
      Real.exp (-(n:ℝ)/(20*q)) := by
  have hh := iid_low_hit_event p H n ((n:ℝ)/(5*q))
    (Finset.univ.filter fun x=>hits H x < (n:ℝ)/(5*q)) (fun x hx=>(Finset.mem_filter.mp hx).2.le)
  refine hh.trans (Real.exp_le_exp.mpr ?_)
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg _
  have hm := mul_le_mul_of_nonneg_right hH hn
  have he : (n:ℝ)/(5*q)-(1/(2*q))*n/2= -(n:ℝ)/(20*q) := by field_simp;ring
  linarith

end SharpRamseyFive.FiniteEntropy

end OAI
