import Mathlib
import OAI.Analysis.CoulombIonization.Fermionic.OccupationPairDensity
import OAI.Analysis.CoulombIonization.Variational.OccupationTraces

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory
open scoped BigOperators ComplexConjugate ContDiff

namespace CoulombAtom

lemma occupation_mean_lower {n : ℕ} {p : Fin n → ℝ}
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (f : (Fin n → Bool) → ℝ) {c : ℝ}
    (h : ∀ m, c ≤ f m) : c ≤ ∑ m : Fin n → Bool, occupationWeight p m * f m := by
  calc
    c = ∑ m : Fin n → Bool, occupationWeight p m * c := by rw [← Finset.sum_mul,occupationWeight_sum,one_mul]
    _ ≤ _ := Finset.sum_le_sum (fun m _ => mul_le_mul_of_nonneg_left (h m) (occupationWeight_nonneg hp m))

def finiteOccupationEnergy {n : ℕ} (Z lam : ℝ) (p : Fin n → ℝ)
    (φ : Fin n → SlaterParticle → ℂ) : ℝ :=
  (1/2:ℝ) * ∑ a : Fin 3, ∑ i : Fin n,
    p i * ∫ z, ‖spatialOrbitalDerivative φ a i z‖^2 ∂slaterParticleMeasure -
    Z * ∑ i : Fin n, p i * ∫ z : SlaterParticle, ‖φ i z‖^2 / ‖z.2‖ ∂slaterParticleMeasure +
    (1/2:ℝ) * ∫ z : SlaterParticle × SlaterParticle,
      (weightedSlaterDensity p φ z.1 * weightedSlaterDensity p φ z.2) / ‖z.1.2-z.2.2‖
        ∂slaterParticleMeasure.prod slaterParticleMeasure + lam * ∑ i : Fin n, p i

lemma occupationSlater_energy_le {n : ℕ} {φ : Fin n → SlaterParticle → ℂ}
    (hφ : ∀ i s, ContDiff ℝ ∞ (fun x : Space => φ i (s,x)))
    (hc : ∀ i s, HasCompactSupport (fun x : Space => φ i (s,x)))
    (ho : ∀ i k, (∫ z, conj (φ i z)*φ k z ∂slaterParticleMeasure) = if i=k then 1 else 0)
    (Z lam : ℝ) (p : Fin n → ℝ) :
    (∑ m : Fin n → Bool, occupationWeight p m *
      (formEnergy Z (slaterForm (occupationOrbitals φ m)) + lam * Fintype.card (Occupied m))) ≤
      finiteOccupationEnergy Z lam p φ := by
  simp only [formEnergy_parts,mul_add,mul_sub,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  simp_rw [mul_left_comm (occupationWeight p _) Z,mul_left_comm (occupationWeight p _) lam]
  rw [← Finset.mul_sum,← Finset.mul_sum,occupationSlater_kinetic hφ hc ho,
    occupationSlater_nuclear hφ hc ho,occupation_count]
  have ht := occupationSlater_repulsion_le_direct hφ hc ho p
  dsimp only [finiteOccupationEnergy]
  linarith

theorem price_le_finite_occupation {n : ℕ} {φ : Fin n → SlaterParticle → ℂ}
    (hφ : ∀ i s, ContDiff ℝ ∞ (fun x : Space => φ i (s,x)))
    (hc : ∀ i s, HasCompactSupport (fun x : Space => φ i (s,x)))
    (ho : ∀ i k, (∫ z, conj (φ i z)*φ k z ∂slaterParticleMeasure) = if i=k then 1 else 0)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam) {p : Fin n → ℝ}
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) :
    priceEnergy (energy Z) lam ≤ finiteOccupationEnergy Z lam p φ := by
  apply le_trans (occupation_mean_lower hp _ _) (occupationSlater_energy_le hφ hc ho Z lam p)
  intro m
  have ht := quantum_price_le_sector hZ hlam (Fintype.card (Occupied m))
  have he := energy_le_form hZ (occupationSlater_admissible hφ hc ho m)
  linarith

end CoulombAtom

end

end OAI
