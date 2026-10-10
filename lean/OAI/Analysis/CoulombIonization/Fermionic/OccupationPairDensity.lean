import Mathlib
import OAI.Analysis.CoulombIonization.Fermionic.SlaterOccupation
import OAI.Analysis.CoulombIonization.Fermionic.WeightedPairDensity
import OAI.Analysis.CoulombIonization.Variational.ComplexOccupation

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_OccupationPairDensity_scope

open scoped BigOperators ComplexConjugate

def slaterPairDensity {n : ℕ} {α : Type*} (φ : Fin n → α → ℂ) (u v : α) : ℝ :=
  (∑ i, ‖φ i u‖^2)*(∑ i, ‖φ i v‖^2) - ‖∑ i, φ i u*conj (φ i v)‖^2

lemma occupationPairDensity {n : ℕ} {α : Type*} (p : Fin n → ℝ)
    (φ : Fin n → α → ℂ) (u v : α) :
    (∑ m : Fin n → Bool, occupationWeight p m *
      slaterPairDensity (occupationOrbitals φ m) u v) =
      weightedSlaterDensity p φ u * weightedSlaterDensity p φ v -
        weightedSlaterExchange p φ u v := by
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum,Complex.ofReal_mul]
  have he (m : Fin n → Bool) :
      (slaterPairDensity (occupationOrbitals φ m) u v : ℂ) =
        ∑ i : Fin n, ∑ j : Fin n, if m i && m j then slaterPairContraction φ i j u v else 0 := by
    rw [slaterPairDensity,← slaterPairContraction_sum]
    exact occupationIndex_pair_sum m (fun i j => slaterPairContraction φ i j u v)
  simp_rw [he]
  rw [occupation_pair_sum_complex p _ (fun i => slaterPairContraction_self φ i u v)]
  exact slaterPairContraction_weighted_sum p φ u v

lemma occupationPairDensity_le_direct {n : ℕ} {α : Type*} (p : Fin n → ℝ)
    (φ : Fin n → α → ℂ) (u v : α) :
    (∑ m : Fin n → Bool, occupationWeight p m *
      slaterPairDensity (occupationOrbitals φ m) u v) ≤
      weightedSlaterDensity p φ u * weightedSlaterDensity p φ v := by
  rw [occupationPairDensity]
  exact sub_le_self _ (sq_nonneg _)

end Work_OccupationPairDensity_scope

section Work_WeightedDirectIntegrable_scope

open MeasureTheory
open scoped BigOperators ContDiff

lemma weightedSlater_direct_coulomb_integrable {n : ℕ} {φ : Fin n → SlaterParticle → ℂ}
    (hφ : ∀ i s, ContDiff ℝ ∞ (fun x : Space => φ i (s,x)))
    (hc : ∀ i s, HasCompactSupport (fun x : Space => φ i (s,x))) (p : Fin n → ℝ) :
    Integrable (fun z : SlaterParticle × SlaterParticle =>
      (weightedSlaterDensity p φ z.1 * weightedSlaterDensity p φ z.2) / ‖z.1.2-z.2.2‖)
      (slaterParticleMeasure.prod slaterParticleMeasure) := by
  have he (z : SlaterParticle × SlaterParticle) :
      (weightedSlaterDensity p φ z.1 * weightedSlaterDensity p φ z.2) / ‖z.1.2-z.2.2‖ =
      ∑ j : Fin n, ∑ i : Fin n, (p i*p j)*((‖φ i z.1‖^2 * ‖φ j z.2‖^2) / ‖z.1.2-z.2.2‖) := by
    simp only [weightedSlaterDensity,Finset.sum_mul,Finset.mul_sum,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp_rw [he]
  exact integrable_finsetSum _ (fun j _ => integrable_finsetSum _ (fun i _ =>
    (orbital_coulomb_product_integrable (hφ i) (hφ j) (hc i) (hc j)).const_mul (p i*p j)))

end Work_WeightedDirectIntegrable_scope

open MeasureTheory
open scoped BigOperators ComplexConjugate ContDiff

lemma slaterPair_coulomb_integrable {n : ℕ} {φ : Fin n → SlaterParticle → ℂ}
    (hφ : ∀ i s, ContDiff ℝ ∞ (fun x : Space => φ i (s,x)))
    (hc : ∀ i s, HasCompactSupport (fun x : Space => φ i (s,x)))
    (ho : ∀ i k, (∫ z, conj (φ i z)*φ k z ∂slaterParticleMeasure) = if i=k then 1 else 0) :
    Integrable (fun z : SlaterParticle × SlaterParticle =>
      slaterPairDensity φ z.1 z.2 / ‖z.1.2-z.2.2‖)
      (slaterParticleMeasure.prod slaterParticleMeasure) := by
  have hl (i : Fin n) := memLp_spinSpace (fun s => (hφ i s).continuous) (hc i)
  have he (z : SlaterParticle × SlaterParticle) :
      slaterPairDensity φ z.1 z.2 / ‖z.1.2-z.2.2‖ =
      ∑ j : Fin n, ∑ k : Fin n, ‖z.1.2-z.2.2‖⁻¹ *
        slaterPairMarginal (μ := slaterParticleMeasure) φ j k z := by
    simp_rw [← Finset.mul_sum]
    rw [slaterPairMarginal_sum hl ho]
    exact div_eq_inv_mul _ _
  simp_rw [he]
  apply integrable_finsetSum
  intro j _
  apply integrable_finsetSum
  intro k _
  by_cases hjk : j ≠ k
  · apply slaterPairMarginal_observable_integrable hjk
    simpa only [div_eq_mul_inv,mul_comm] using slater_coulomb_integrable hφ hc j k hjk
  · simp only [slaterPairMarginal,ite_eq_right hjk,mul_zero]
    exact integrable_zero _ _ _

lemma occupationSlater_repulsion {n : ℕ} {φ : Fin n → SlaterParticle → ℂ}
    (hφ : ∀ i s, ContDiff ℝ ∞ (fun x : Space => φ i (s,x)))
    (hc : ∀ i s, HasCompactSupport (fun x : Space => φ i (s,x)))
    (ho : ∀ i k, (∫ z, conj (φ i z)*φ k z ∂slaterParticleMeasure) = if i=k then 1 else 0)
    (p : Fin n → ℝ) :
    (∑ m : Fin n → Bool, occupationWeight p m *
      formRepulsion (slaterForm (occupationOrbitals φ m))) =
      (1/2:ℝ) * ∫ z : SlaterParticle × SlaterParticle,
        (weightedSlaterDensity p φ z.1 * weightedSlaterDensity p φ z.2 -
          weightedSlaterExchange p φ z.1 z.2) / ‖z.1.2-z.2.2‖
          ∂slaterParticleMeasure.prod slaterParticleMeasure := by
  have hi (m : Fin n → Bool) := slaterPair_coulomb_integrable
    (occupationOrbitals_smooth hφ m) (occupationOrbitals_compact hc m)
    (occupationOrbitals_orthonormal ho m)
  have ht (m : Fin n → Bool) := slaterForm_repulsion
    (occupationOrbitals_smooth hφ m) (occupationOrbitals_compact hc m)
    (occupationOrbitals_orthonormal ho m)
  simp_rw [ht]
  calc
    _ = (1/2:ℝ) * ∑ m : Fin n → Bool, ∫ z : SlaterParticle × SlaterParticle,
        occupationWeight p m * (slaterPairDensity (occupationOrbitals φ m) z.1 z.2 /
          ‖z.1.2-z.2.2‖) ∂slaterParticleMeasure.prod slaterParticleMeasure := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      rw [integral_const_mul]
      change occupationWeight p m * ((1/2:ℝ) *
        (∫ z : SlaterParticle × SlaterParticle, slaterPairDensity (occupationOrbitals φ m) z.1 z.2 /
          ‖z.1.2-z.2.2‖ ∂slaterParticleMeasure.prod slaterParticleMeasure)) = _
      ring
    _ = (1/2:ℝ) * ∫ z : SlaterParticle × SlaterParticle,
        ∑ m : Fin n → Bool, occupationWeight p m *
          (slaterPairDensity (occupationOrbitals φ m) z.1 z.2 / ‖z.1.2-z.2.2‖)
          ∂slaterParticleMeasure.prod slaterParticleMeasure := by
      rw [integral_finsetSum _ (fun m _ => (hi m).const_mul _)]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with z
      simp only [← mul_div_assoc,← Finset.sum_div,occupationPairDensity]

lemma occupationSlater_repulsion_le_direct {n : ℕ} {φ : Fin n → SlaterParticle → ℂ}
    (hφ : ∀ i s, ContDiff ℝ ∞ (fun x : Space => φ i (s,x)))
    (hc : ∀ i s, HasCompactSupport (fun x : Space => φ i (s,x)))
    (ho : ∀ i k, (∫ z, conj (φ i z)*φ k z ∂slaterParticleMeasure) = if i=k then 1 else 0)
    (p : Fin n → ℝ) :
    (∑ m : Fin n → Bool, occupationWeight p m *
      formRepulsion (slaterForm (occupationOrbitals φ m))) ≤
      (1/2:ℝ) * ∫ z : SlaterParticle × SlaterParticle,
        (weightedSlaterDensity p φ z.1 * weightedSlaterDensity p φ z.2) / ‖z.1.2-z.2.2‖
          ∂slaterParticleMeasure.prod slaterParticleMeasure := by
  rw [occupationSlater_repulsion hφ hc ho p]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  have hi : Integrable (fun z : SlaterParticle × SlaterParticle =>
      (weightedSlaterDensity p φ z.1 * weightedSlaterDensity p φ z.2 -
        weightedSlaterExchange p φ z.1 z.2) / ‖z.1.2-z.2.2‖)
        (slaterParticleMeasure.prod slaterParticleMeasure) := by
    have he (z : SlaterParticle × SlaterParticle) :
        (weightedSlaterDensity p φ z.1 * weightedSlaterDensity p φ z.2 -
          weightedSlaterExchange p φ z.1 z.2) / ‖z.1.2-z.2.2‖ =
        ∑ m : Fin n → Bool, occupationWeight p m *
          (slaterPairDensity (occupationOrbitals φ m) z.1 z.2 / ‖z.1.2-z.2.2‖) := by
      simp only [← mul_div_assoc,← Finset.sum_div,occupationPairDensity]
    simp_rw [he]
    exact integrable_finsetSum _ (fun m _ => (slaterPair_coulomb_integrable
      (occupationOrbitals_smooth hφ m) (occupationOrbitals_compact hc m)
      (occupationOrbitals_orthonormal ho m)).const_mul _)
  apply integral_mono hi (weightedSlater_direct_coulomb_integrable hφ hc p)
  intro z
  exact div_le_div_of_nonneg_right (sub_le_self _ (sq_nonneg _)) (norm_nonneg _)

end CoulombAtom

end

end OAI
