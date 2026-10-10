import Mathlib
import OAI.Combinatorics.KMedian.Process.BatchEstimate
import OAI.Combinatorics.KMedian.Sparse.SparseEnumeratedBatch

namespace OAI

namespace MetricKMedian.SparseEnumeratedBatch
open Finset
variable {E : Type} [DecidableEq E] [Fintype E] {n : ℕ}

theorem relevant_generator_estimate (enum : Fin n ≃ E) (Z R : Finset E) (C : E → Finset E)
    (p : ℚ) (q : E → ℚ) (b : E → ℝ) (hp : 0 ≤ p ∧ p ≤ 1)
    (hq0 : ∀ e, 0 ≤ q e ∧ q e ≤ 1)
    {φ K Q : ℝ} {N : ℕ} (hφ : 0 ≤ φ) (hK : 0 ≤ K) (hQ : 0 ≤ Q)
    (hpQ : (p:ℝ) ≤ Q) (hqQ : ∀ e, (q e:ℝ) ≤ Q)
    (hq : ∀ e, (p:ℝ) ≤ q e ∧ (q e:ℝ) ≤ (1+φ)*p)
    (hC : ∀ e, (C e).card ≤ N) (hself : ∀ e, e ∉ C e)
    (D : Finset E → ℝ)
    (hb : ∀ e ∈ R, |b e| ≤ K) (hD : ∀ A, D A ≤ K)
    (hzero : ∀ A, A ∩ R=∅ → D A ≤ 0)
    (hone : ∀ A e, A ∩ R={e} → D A ≤ b e) :
    (law enum Z C p q hp hq0).real.expect D ≤
      ((p:ℝ)/2)*(∑ e ∈ R, b e)+(R.card:ℝ)*K*((N:ℝ)*(p:ℝ)^2/2+φ*(p:ℝ)/2)+
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
      |(law enum Z C p q hp hq0).real.prob (fun A => e ∈ A' A)-(p:ℝ)/2| ≤
        (N:ℝ)*(p:ℝ)^2/2+φ*(p:ℝ)/2 := by
    intro e
    simpa only [A', mem_filter, mem_univ, true_and] using
      marginal_error enum Z C p q hp hq0 hφ hq hC hself e.val
  have hpair : ∀ e f : R, e ≠ f →
      (law enum Z C p q hp hq0).real.prob (fun A => e ∈ A' A ∧ f ∈ A' A) ≤ Q^2 := by
    intro e f hef
    have h2 := pair_le enum Z C p q hp hq0 e.val f.val
      (show e.val ≠ f.val from fun h => hef (Subtype.ext h))
    have hpp : (p:ℝ)^2 ≤ Q^2 := (sq_le_sq₀ (by exact_mod_cast hp.1) hQ).mpr hpQ
    have hqq := mul_le_mul (hqQ e.val) (hqQ f.val) (show (0:ℝ) ≤ q f.val by exact_mod_cast (hq0 f.val).1) hQ
    simp only [A', mem_filter, mem_univ, true_and]
    nlinarith only [h2, hpp, hqq]
  have h := BatchRemainder.generator_estimate (law enum Z C p q hp hq0).real A'
    (fun e : R => b e.val) D hK (by
      have hpR : (0:ℝ) ≤ p := by exact_mod_cast hp.1
      positivity)
    (fun e => hb e.val e.property) hD (fun A ha => hzero A (hzero' A ha))
    (fun A e ha => hone A e.val (hone' A e ha)) hfirst hpair
  simpa only [Fintype.card_coe, sum_coe_sort] using h

end MetricKMedian.SparseEnumeratedBatch

end OAI
