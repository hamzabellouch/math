import OAI.NumberTheory.Ostmann.Dirichlet.PrimeSeriesTailKernel

namespace OAI

noncomputable section
namespace Ostmann.Dirichlet
open MeasureTheory
open scoped BigOperators

theorem sum_ordinaryPrimeSeries_tail_le (P : Finset ℕ) {σ Q : ℝ}
    (hσ : 1 < σ) (hQ : 0 < Q) (hprime : ∀ p ∈ P, p.Prime)
    (hPQ : ∀ p ∈ P, Q < (p : ℝ)) :
    (∑ p ∈ P, ordinaryPrimeSeriesTerm σ p) ≤
      Real.log 4 * σ / (σ - 1) * Q ^ (1 - σ) := by
  have hk : ∀ p ∈ P, IntegrableOn (primeSeriesTailKernel σ p) (Set.Ioi Q) :=
    fun p _ => primeSeriesTailKernel_integrable hσ hQ p
  have hm : IntegrableOn (fun t : ℝ => Real.log 4 * σ * t ^ (-σ)) (Set.Ioi Q) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : -σ < -1) hQ).const_mul _
  calc
    _ = ∫ t in Set.Ioi Q, ∑ p ∈ P, primeSeriesTailKernel σ p t := by
      rw [integral_finsetSum P hk]
      exact Finset.sum_congr rfl (fun p hp => (primeSeriesTailKernel_integral hσ (hprime p hp) (hPQ p hp).le).symm)
    _ ≤ ∫ t in Set.Ioi Q, Real.log 4 * σ * t ^ (-σ) := by
      apply setIntegral_mono_on (integrable_finsetSum P hk) hm measurableSet_Ioi
      intro t ht
      exact primeSeriesTailKernel_sum_bound P (by linarith) (hQ.trans ht) hprime
    _ = _ := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith : -σ < -1) hQ]
      rw [show -σ + 1 = 1 - σ by ring]
      have hne : σ - 1 ≠ 0 := by linarith
      have hne' : 1 - σ ≠ 0 := by linarith
      field_simp
      ring

def ordinaryPrimeTailTerm (σ Q : ℝ) (n : ℕ) : ℝ :=
  if n.Prime ∧ Q < (n : ℝ) then Real.log n / (n : ℝ) ^ σ else 0

lemma ordinaryPrimeTailTerm_nonneg (σ Q : ℝ) (n : ℕ) : 0 ≤ ordinaryPrimeTailTerm σ Q n := by
  unfold ordinaryPrimeTailTerm
  split_ifs with hn
  · exact div_nonneg (Real.log_nonneg (by exact_mod_cast hn.1.one_le))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  · rfl

lemma sum_ordinaryPrimeTailTerm_le (S : Finset ℕ) {σ Q : ℝ} (hσ : 1 < σ) (hQ : 0 < Q) :
    (∑ n ∈ S, ordinaryPrimeTailTerm σ Q n) ≤
      Real.log 4 * σ / (σ - 1) * Q ^ (1 - σ) := by
  classical
  let P : Finset ℕ := S.filter (fun (p : ℕ) => p.Prime ∧ Q < (p : ℝ))
  have h := sum_ordinaryPrimeSeries_tail_le P hσ hQ
    (fun p hp => (Finset.mem_filter.mp hp).2.1)
    (fun p hp => (Finset.mem_filter.mp hp).2.2)
  have he : (∑ p ∈ P, ordinaryPrimeSeriesTerm σ p) = ∑ n ∈ S, ordinaryPrimeTailTerm σ Q n := by
    rw [show P = S.filter (fun (p : ℕ) => p.Prime ∧ Q < (p : ℝ)) from rfl, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hcond : p.Prime ∧ Q < (p : ℝ)
    · simp only [ordinaryPrimeTailTerm, ordinaryPrimeSeriesTerm, hcond, ite_true]
    · simp only [ordinaryPrimeTailTerm, hcond, ite_false]
  rwa [he] at h

theorem ordinaryPrimeTail_summable {σ Q : ℝ} (hσ : 1 < σ) (hQ : 0 < Q) :
    Summable (ordinaryPrimeTailTerm σ Q) :=
  summable_of_sum_le (fun n => ordinaryPrimeTailTerm_nonneg σ Q n)
    (fun S => sum_ordinaryPrimeTailTerm_le S hσ hQ)

theorem ordinaryPrimeTail_le {σ Q : ℝ} (hσ : 1 < σ) (hQ : 0 < Q) :
    (∑' n : ℕ, if n.Prime ∧ Q < (n : ℝ) then Real.log n / (n : ℝ) ^ σ else 0) ≤
      Real.log 4 * σ / (σ - 1) * Q ^ (1 - σ) := by
  exact Real.tsum_le_of_sum_le (fun n => ordinaryPrimeTailTerm_nonneg σ Q n)
    (fun S => sum_ordinaryPrimeTailTerm_le S hσ hQ)

end Ostmann.Dirichlet

end

end OAI
