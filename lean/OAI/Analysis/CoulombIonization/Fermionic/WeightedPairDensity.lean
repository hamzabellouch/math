import Mathlib
import OAI.Analysis.CoulombIonization.Fermionic.SlaterPairTrace

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open scoped BigOperators ComplexConjugate

namespace CoulombAtom

def weightedSlaterDensity {n : ℕ} {α : Type*} (p : Fin n → ℝ)
    (φ : Fin n → α → ℂ) (u : α) : ℝ := ∑ i, p i * ‖φ i u‖^2

def weightedSlaterExchange {n : ℕ} {α : Type*} (p : Fin n → ℝ)
    (φ : Fin n → α → ℂ) (u v : α) : ℝ :=
  ‖∑ i : Fin n, (p i : ℂ) * (φ i u * conj (φ i v))‖^2

lemma weightedSlaterDensity_nonneg {n : ℕ} {α : Type*} {p : Fin n → ℝ}
    (hp : ∀ i, 0 ≤ p i) (φ : Fin n → α → ℂ) (u : α) : 0 ≤ weightedSlaterDensity p φ u :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (hp i) (sq_nonneg _))

lemma slaterPairContraction_weighted_sum {n : ℕ} {α : Type*}
    (p : Fin n → ℝ) (φ : Fin n → α → ℂ) (u v : α) :
    (∑ i : Fin n, ∑ l : Fin n, (p i : ℂ)*(p l : ℂ)*slaterPairContraction φ i l u v) =
      (Complex.ofReal (weightedSlaterDensity p φ u * weightedSlaterDensity p φ v -
        weightedSlaterExchange p φ u v)) := by
  have hnorm (z : ℂ) : Complex.ofReal (‖z‖^2) = conj z*z := by
    simpa only [Complex.sq_norm] using Complex.normSq_eq_conj_mul_self (z := z)
  simp only [weightedSlaterDensity,weightedSlaterExchange,Complex.ofReal_sub,
    Complex.ofReal_mul,Complex.ofReal_sum,hnorm]
  simp only [slaterPairContraction,mul_sub,Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro l _
    simp only [map_mul]
    ring
  · simp only [map_sum,map_mul,starRingEnd_self_apply,Complex.conj_ofReal]
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro l _
    ring

end CoulombAtom

end

end OAI
