import Mathlib
import OAI.Analysis.CoulombIonization.Fermionic.SlaterOccupation

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory
open scoped BigOperators ComplexConjugate ContDiff

namespace CoulombAtom

lemma slaterForm_zeroAt {n : ℕ} (φ : Fin n → SlaterParticle → ℂ)
    (x : Configuration n) (j : Fin n)
    (hz : ∀ i s, x j ∉ tsupport (fun y : Space => φ i (s,y))) :
    FormZeroAt (slaterForm φ) x := by
  have hv (i : Fin n) (s : Fin 2) : φ i (s,x j) = 0 := image_eq_zero_of_notMem_tsupport (f := fun y : Space => φ i (s,y)) (hz i s)
  have hd (a : Fin 3) (i : Fin n) (s : Fin 2) : spatialOrbitalDerivative φ a i (s,x j) = 0 := by
    rw [spatialOrbitalDerivative, fderiv_of_notMem_tsupport ℝ (hz i s)]
    rfl
  intro s
  constructor
  · change _ * slaterRaw φ (slaterParticles s x) = 0
    suffices hs : slaterRaw φ (slaterParticles s x) = 0 by rw [hs,mul_zero]
    apply Finset.sum_eq_zero
    intro σ _
    suffices hs : slaterTensor φ σ (slaterParticles s x) = 0 by rw [hs,mul_zero]
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    exact hv (σ j) (s j)
  · intro k a
    change _ * slaterCoordinateRaw φ (spatialOrbitalDerivative φ a) k (slaterParticles s x) = 0
    suffices hs : slaterCoordinateRaw φ (spatialOrbitalDerivative φ a) k (slaterParticles s x) = 0 by rw [hs,mul_zero]
    apply Finset.sum_eq_zero
    intro σ _
    suffices hs : slaterCoordinateTensor φ (spatialOrbitalDerivative φ a) k σ (slaterParticles s x) = 0 by rw [hs,mul_zero]
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    by_cases hjk : j = k
    · simp only [ite_eq_left hjk,slaterParticles]
      exact hd a (σ j) (s j)
    · simp only [ite_eq_right hjk,slaterParticles]
      exact hv (σ j) (s j)

lemma occupationSlater_outside {n : ℕ} (φ : Fin n → SlaterParticle → ℂ)
    (A : Set Space) (hs : ∀ i s, Disjoint A (tsupport (fun y : Space => φ i (s,y))))
    (m : Fin n → Bool) :
    ∀ x j, x j ∈ A → FormZeroAt (slaterForm (occupationOrbitals φ m)) x := by
  intro x j hx
  apply slaterForm_zeroAt _ x j
  intro i s hi
  exact Set.disjoint_left.mp (hs (occupationIndex m i) s) hx hi

end CoulombAtom

end

end OAI
