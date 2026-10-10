import Mathlib
import OAI.Combinatorics.KMedian.Probability.FiniteProcess
import OAI.Combinatorics.KMedian.Probability.BernoulliRealTransfer

namespace OAI

namespace MetricKMedian.FiniteLaw
open Finset
variable {Ω E : Type} [Fintype Ω] [Fintype E] [DecidableEq E]

theorem prob_le_add_of_imp (μ : FiniteLaw Ω) (A B C : Ω → Prop)
    [DecidablePred A] [DecidablePred B] [DecidablePred C]
    (h : ∀ ω, A ω → B ω ∨ C ω) : μ.prob A ≤ μ.prob B+μ.prob C := by
  rw [prob,prob,prob,← expect_add]
  apply μ.expect_mono
  intro ω
  by_cases ha : A ω
  · rcases h ω ha with hb | hc
    · simp only [ite_eq_left ha,ite_eq_left hb]
      split_ifs <;> norm_num
    · simp only [ite_eq_left ha,ite_eq_left hc]
      split_ifs <;> norm_num
  · simp only [ite_eq_right ha]
    split_ifs <;> norm_num

theorem filtered_two_moment (μ : FiniteLaw (E → Bool)) (C : E → Finset E)
    (p : ℝ) (hm : ∀ e, μ.prob (fun q => q e=true)=p)
    (hp : ∀ e f, e≠f → μ.prob (fun q => q e=true ∧ q f=true) ≤ p^2)
    (e : E) (hself : e∉C e) :
    |μ.prob (fun q => e∈selected C q)-p| ≤ (C e).card*p^2 := by
  classical
  have hu : μ.prob (fun q => e∈selected C q) ≤ p := by
    rw [← hm e]
    exact μ.prob_mono (fun q h => (mem_filter.mp h).2.1)
  have hd := μ.prob_le_add_of_imp (fun q => q e=true)
    (fun q => e∈selected C q) (fun q => ∃ f∈C e, q e=true ∧ q f=true) (by
      intro q he
      by_cases hh : ∀ f∈C e, q f=false
      · exact Or.inl (mem_filter.mpr ⟨mem_univ _,he,hh⟩)
      · push Not at hh
        obtain ⟨f,hf,hff⟩ := hh
        have hft : q f=true := by cases hq : q f <;> simp_all
        exact Or.inr ⟨f,hf,he,hft⟩)
  rw [hm e] at hd
  have hb := μ.prob_exists_le_sum (C e) (fun f q => q e=true ∧ q f=true)
  have hs : (∑ f∈C e, μ.prob (fun q => q e=true ∧ q f=true)) ≤ (C e).card*p^2 := by
    calc
      _ ≤ ∑ _f∈C e, p^2 := sum_le_sum (fun f hf => hp e f (fun he => hself (he ▸ hf)))
      _ = _ := by simp
  rw [abs_of_nonpos (sub_nonpos.mpr hu)]
  linarith only [hd,hb,hs]

end MetricKMedian.FiniteLaw
namespace MetricKMedian.SparseBernoulli
open Finset
variable {n d : ℕ}

theorem cylinder (p : Fin n → ℚ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (S : Finset (Fin n)) (hS : S.card ≤ d) :
    (run (d := d) p hp n).real.prob (fun q => ∀ i∈S, q i=true)=((∏ i∈S,p i:ℚ):ℝ) := by
  calc
    _ = (run (d := d) p hp n).real.expect (fun q => ((∏ i∈S,flag q i:ℚ):ℝ)) := by
      unfold FiniteLaw.prob
      congr 1
      funext q
      rw [product_indicator]
      split_ifs <;> norm_num
    _ = _ := by rw [SparseIntegerLaw.real_expect,subset_moment p hp S hS]

theorem real_marginal (p : Fin n → ℚ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (hd : 1 ≤ d) (e : Fin n) :
    (run (d := d) p hp n).real.prob (fun q => q e=true)=(p e:ℝ) := by
  have he := cylinder (d := d) p hp {e} (by simpa using hd)
  simpa only [mem_singleton,forall_eq,prod_singleton] using he

theorem real_pair (p : Fin n → ℚ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (hd : 2 ≤ d) (e f : Fin n) (hef : e≠f) :
    (run (d := d) p hp n).real.prob (fun q => q e=true ∧ q f=true)=(p e:ℝ)*(p f:ℝ) := by
  have he := cylinder (d := d) p hp {e,f} (by simpa [hef] using hd)
  simpa only [mem_insert,mem_singleton,forall_eq_or_imp,forall_eq,prod_pair hef,Rat.cast_mul] using he

theorem filtered_error (p : ℚ) (hp : 0 ≤ p ∧ p ≤ 1) (hd : 2 ≤ d)
    (C : Fin n → Finset (Fin n)) (e : Fin n) (hself : e∉C e) :
    |(run (d := d) (fun _ => p) (fun _ => hp) n).real.prob
      (fun q => e∈FiniteLaw.selected C q)-(p:ℝ)| ≤ (C e).card*(p:ℝ)^2 := by
  apply FiniteLaw.filtered_two_moment _ C (p:ℝ)
    (fun i => real_marginal _ _ (by omega) i) ?_ e hself
  intro i j hij
  rw [real_pair _ _ hd i j hij,pow_two]

end MetricKMedian.SparseBernoulli

end OAI
