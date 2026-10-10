import Mathlib
import OAI.Analysis.CoulombIonization.Fermionic.SlaterOccupation

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory
open scoped BigOperators ComplexConjugate ContDiff

namespace CoulombAtom

lemma occupation_expect_sum {n : ℕ} {α : Type*} [Fintype α] (p : Fin n → ℝ)
    (f : (Fin n → Bool) → α → ℝ) :
    (∑ m : Fin n → Bool, occupationWeight p m * ∑ a, f m a) =
      ∑ a, ∑ m : Fin n → Bool, occupationWeight p m * f m a := by
  simp only [Finset.mul_sum]
  exact Finset.sum_comm

lemma occupation_count {n : ℕ} (p : Fin n → ℝ) :
    (∑ m : Fin n → Bool, occupationWeight p m * (Fintype.card (Occupied m) : ℝ)) =
      ∑ i : Fin n, p i := by
  have he (m : Fin n → Bool) : (Fintype.card (Occupied m) : ℝ) =
      ∑ i : Fin n, if m i then (1:ℝ) else 0 := by
    rw [← occupationIndex_sum m (fun _ => (1:ℝ))]
    simp
  simp_rw [he,occupation_sum,mul_one]

lemma occupationSlater_kinetic {n : ℕ} {φ : Fin n → SlaterParticle → ℂ}
    (hφ : ∀ i s, ContDiff ℝ ∞ (fun x : Space => φ i (s,x)))
    (hc : ∀ i s, HasCompactSupport (fun x : Space => φ i (s,x)))
    (ho : ∀ i k, (∫ z, conj (φ i z)*φ k z ∂slaterParticleMeasure) = if i=k then 1 else 0)
    (p : Fin n → ℝ) :
    (∑ m : Fin n → Bool, occupationWeight p m * formKinetic (slaterForm (occupationOrbitals φ m))) =
      (1/2:ℝ) * ∑ a : Fin 3, ∑ i : Fin n,
        p i * ∫ z, ‖spatialOrbitalDerivative φ a i z‖^2 ∂slaterParticleMeasure := by
  have he (m : Fin n → Bool) : formKinetic (slaterForm (occupationOrbitals φ m)) =
      (1/2:ℝ)*∑ a : Fin 3, ∑ i : Fin n, if m i then
        (∫ z, ‖spatialOrbitalDerivative φ a i z‖^2 ∂slaterParticleMeasure) else 0 := by
    rw [slaterForm_kinetic (occupationOrbitals_smooth hφ m) (occupationOrbitals_compact hc m)
      (occupationOrbitals_orthonormal ho m)]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    exact occupationIndex_sum m (fun i => ∫ z, ‖spatialOrbitalDerivative φ a i z‖^2 ∂slaterParticleMeasure)
  calc
    _ = (1/2:ℝ)*∑ m : Fin n → Bool, occupationWeight p m *
        ∑ a : Fin 3, ∑ i : Fin n, if m i then
          (∫ z, ‖spatialOrbitalDerivative φ a i z‖^2 ∂slaterParticleMeasure) else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      rw [he]
      ring
    _ = _ := by rw [occupation_expect_sum]; simp_rw [occupation_sum]

lemma occupationSlater_nuclear {n : ℕ} {φ : Fin n → SlaterParticle → ℂ}
    (hφ : ∀ i s, ContDiff ℝ ∞ (fun x : Space => φ i (s,x)))
    (hc : ∀ i s, HasCompactSupport (fun x : Space => φ i (s,x)))
    (ho : ∀ i k, (∫ z, conj (φ i z)*φ k z ∂slaterParticleMeasure) = if i=k then 1 else 0)
    (p : Fin n → ℝ) :
    (∑ m : Fin n → Bool, occupationWeight p m * formNuclear (slaterForm (occupationOrbitals φ m))) =
      ∑ i : Fin n, p i * ∫ z : SlaterParticle, ‖φ i z‖^2 / ‖z.2‖ ∂slaterParticleMeasure := by
  have he (m : Fin n → Bool) : formNuclear (slaterForm (occupationOrbitals φ m)) =
      ∑ i : Fin n, if m i then (∫ z : SlaterParticle, ‖φ i z‖^2 / ‖z.2‖ ∂slaterParticleMeasure) else 0 := by
    rw [slaterForm_nuclear (occupationOrbitals_smooth hφ m) (occupationOrbitals_compact hc m)
      (occupationOrbitals_orthonormal ho m)]
    exact occupationIndex_sum m (fun i => ∫ z : SlaterParticle, ‖φ i z‖^2 / ‖z.2‖ ∂slaterParticleMeasure)
  simp_rw [he,occupation_sum]

end CoulombAtom

end

end OAI
