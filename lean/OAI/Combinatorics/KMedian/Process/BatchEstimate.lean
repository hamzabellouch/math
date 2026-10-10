import Mathlib
import OAI.Combinatorics.KMedian.Process.PhysicalBatchLaw

namespace OAI

namespace MetricKMedian.BatchRemainder
open Finset

variable {Ω E : Type*} [Fintype Ω] [Fintype E] [DecidableEq E]

theorem generator_estimate (μ : FiniteLaw Ω) (A : Ω → Finset E) (b : E → ℝ)
    (D : Ω → ℝ) {K lam δ J : ℝ} (hK : 0 ≤ K) (hδ : 0 ≤ δ)
    (hb : ∀ e, |b e| ≤ K) (hD : ∀ ω, D ω ≤ K)
    (hzero : ∀ ω, A ω=∅ → D ω ≤ 0)
    (hone : ∀ ω e, A ω={e} → D ω ≤ b e)
    (hfirst : ∀ e, |μ.prob (fun ω => e ∈ A ω)-lam| ≤ δ)
    (hpair : ∀ e f, e ≠ f → μ.prob (fun ω => e ∈ A ω ∧ f ∈ A ω) ≤ J) :
    μ.expect D ≤ lam*(∑ e, b e)+(Fintype.card E:ℝ)*K*δ+
      2*K*((univ : Finset E).offDiag.card:ℝ)*J := by
  have hfirstsum : (∑ e, μ.prob (fun ω => e ∈ A ω)*b e) ≤
      lam*(∑ e, b e)+(Fintype.card E:ℝ)*K*δ := by
    have hpoint : ∀ e, μ.prob (fun ω => e ∈ A ω)*b e ≤ lam*b e+K*δ := by
      intro e
      have habs : |(μ.prob (fun ω => e ∈ A ω)-lam)*b e| ≤ δ*K := by
        rw [abs_mul]
        exact mul_le_mul (hfirst e) (hb e) (abs_nonneg _) hδ
      have hle := (le_abs_self ((μ.prob (fun ω => e ∈ A ω)-lam)*b e)).trans habs
      nlinarith only [hle]
    have hsum := sum_le_sum (fun e (_ : e ∈ (univ : Finset E)) => hpoint e)
    simpa only [sum_add_distrib, ← mul_sum, sum_const, card_univ, nsmul_eq_mul, mul_assoc, mul_left_comm, mul_comm]
      using hsum
  have hpairSum : (∑ p ∈ (univ : Finset E).offDiag,
      μ.prob (fun ω => p.1 ∈ A ω ∧ p.2 ∈ A ω)) ≤ ((univ : Finset E).offDiag.card:ℝ)*J := by
    calc
      _ ≤ ∑ _p ∈ (univ : Finset E).offDiag, J :=
        sum_le_sum (fun p hp => hpair p.1 p.2 (mem_offDiag.mp hp).2.2)
      _ = _ := by simp only [sum_const, nsmul_eq_mul]
  have hbase := expectation_le μ A b D hK (fun e => (abs_le.mp (hb e)).1) hD hzero hone
  have hj := mul_le_mul_of_nonneg_left hpairSum (by positivity : 0 ≤ 2*K)
  nlinarith only [hbase, hfirstsum, hj]

end MetricKMedian.BatchRemainder

namespace MetricKMedian.PhysicalBatchLaw
open Finset
variable {E : Type*} [Fintype E] [DecidableEq E]

theorem relevant_generator_estimate (Z R : Finset E) (C : E → Finset E)
    (p : ℝ) (q b : E → ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    {φ K Q : ℝ} {N : ℕ} (hφ : 0 ≤ φ) (hK : 0 ≤ K) (hQ : 0 ≤ Q)
    (hpQ : p ≤ Q) (hqQ : ∀ e, q e ≤ Q)
    (hq : ∀ e, p ≤ q e ∧ q e ≤ (1+φ)*p)
    (hC : ∀ e, (C e).card ≤ N) (hself : ∀ e, e ∉ C e)
    (D : Finset E → ℝ)
    (hb : ∀ e ∈ R, |b e| ≤ K) (hD : ∀ A, D A ≤ K)
    (hzero : ∀ A, A ∩ R=∅ → D A ≤ 0)
    (hone : ∀ A e, A ∩ R={e} → D A ≤ b e) :
    (law Z C p q hp0 hp1 hq0 hq1).expect D ≤
      (p/2)*(∑ e ∈ R, b e)+(R.card:ℝ)*K*((N:ℝ)*p^2/2+φ*p/2)+
        2*K*((univ : Finset R).offDiag.card:ℝ)*Q^2 := by
  let A' : Finset E → Finset R := fun A => univ.filter (fun e : R => e.val ∈ A)
  have hzero' : ∀ A, A' A=∅ → A ∩ R=∅ := by
    intro A ha
    apply eq_empty_iff_forall_notMem.mpr
    intro e he
    have he' : (⟨e, (mem_inter.mp he).2⟩ : R) ∈ A' A := by
      simp only [A', mem_filter, mem_univ, true_and]
      exact (mem_inter.mp he).1
    rw [ha] at he'
    exact notMem_empty _ he'
  have hone' : ∀ A (e : R), A' A={e} → A ∩ R={e.val} := by
    intro A e ha
    ext f
    constructor
    · intro hf
      have hf' : (⟨f, (mem_inter.mp hf).2⟩ : R) ∈ A' A := by
        simp only [A', mem_filter, mem_univ, true_and]
        exact (mem_inter.mp hf).1
      rw [ha, mem_singleton] at hf'
      simpa only [mem_singleton] using congrArg Subtype.val hf'
    · intro hf
      have hfval : f=e.val := mem_singleton.mp hf
      subst f
      have he : e ∈ A' A := by rw [ha]; exact mem_singleton_self _
      exact mem_inter.mpr ⟨(mem_filter.mp he).2, e.property⟩
  have hfirst : ∀ e : R,
      |(law Z C p q hp0 hp1 hq0 hq1).prob (fun A => e ∈ A' A)-p/2| ≤
        (N:ℝ)*p^2/2+φ*p/2 := by
    intro e
    simpa only [A', mem_filter, mem_univ, true_and] using
      marginal_error Z C p q hp0 hp1 hq0 hq1 hφ hq hC hself e.val
  have hpair : ∀ e f : R, e ≠ f →
      (law Z C p q hp0 hp1 hq0 hq1).prob (fun A => e ∈ A' A ∧ f ∈ A' A) ≤ Q^2 := by
    intro e f hef
    have h2 := pair_le Z C p q hp0 hp1 hq0 hq1
      (show e.val ≠ f.val from fun h => hef (Subtype.ext h))
    have hpp : p^2 ≤ Q^2 := (sq_le_sq₀ hp0 hQ).mpr hpQ
    have hqq := mul_le_mul (hqQ e.val) (hqQ f.val) (hq0 f.val) hQ
    simp only [A', mem_filter, mem_univ, true_and]
    nlinarith only [h2, hpp, hqq]
  have h := BatchRemainder.generator_estimate (law Z C p q hp0 hp1 hq0 hq1) A'
    (fun e : R => b e.val) D hK (by positivity)
    (fun e => hb e.val e.property) hD (fun A ha => hzero A (hzero' A ha))
    (fun A e ha => hone A e.val (hone' A e ha)) hfirst hpair
  simpa only [Fintype.card_coe, sum_coe_sort] using h

end MetricKMedian.PhysicalBatchLaw

end OAI
