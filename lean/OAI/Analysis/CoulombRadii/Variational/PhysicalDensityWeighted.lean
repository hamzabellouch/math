import Mathlib
import OAI.Analysis.CoulombRadii.Variational.PhysicalBridge
import OAI.Analysis.CoulombRadii.FieldAnalysis.PoissonInterior

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
noncomputable section
namespace NeutralAtom

theorem density_weight_eq_first_site {N : ℕ} (ψ : Wavefunction (N+1))
    (W : Position → ℝ)
    (hi : ∀ σ,Integrable (fun x : Configuration (N+1) => W (x 0)*‖ψ σ x‖^2)) :
    (∫ z,W z*density ψ z)=(N+1:ℝ)*rawExpectation ψ (fun x => W (x 0)) := by
  have hw (σ : Spins (N+1)) := (integrable_cons (hi σ)).integral_prod_left
  have he (σ : Spins (N+1)) :
      (fun z => W z*(∫ x : Configuration N,‖ψ σ (Fin.cons z x)‖^2))=
      fun z => ∫ x : Configuration N,W z*‖ψ σ (Fin.cons z x)‖^2 := by
    funext z
    rw [integral_const_mul]
  have hw' (σ : Spins (N+1)) : Integrable (fun z => W z*(∫ x : Configuration N,‖ψ σ (Fin.cons z x)‖^2)) := by
    rw [he]
    simpa only [Fin.cons_zero] using hw σ
  unfold density rawExpectation configurationDensity
  simp_rw [mul_left_comm (W _) (N+1:ℝ)]
  rw [integral_const_mul]
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun σ _ => hw' σ),
    integral_finsetSum _ (fun σ _ => hi σ)]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  simp_rw [he σ]
  simpa only [Fin.cons_zero] using integral_cons (hi σ)

theorem density_weight_integrable {N : ℕ} (ψ : Wavefunction (N+1))
    (W : Position → ℝ)
    (hi : ∀ σ,Integrable (fun x : Configuration (N+1) => W (x 0)*‖ψ σ x‖^2)) :
    Integrable (fun z => W z*density ψ z) := by
  have hw (σ : Spins (N+1)) := (integrable_cons (hi σ)).integral_prod_left
  have hh : (fun z => W z*density ψ z)=fun z => (N+1:ℝ)*
      ∑ σ : Spins (N+1),∫ x : Configuration N,W z*‖ψ σ (Fin.cons z x)‖^2 := by
    funext z
    simp only [density,integral_const_mul,←Finset.mul_sum]
    ring
  rw [hh]
  apply Integrable.const_mul
  exact integrable_finsetSum _ (fun σ _ => by simpa only [Fin.cons_zero] using hw σ)

theorem rawExpectation_oneBody_eq_density {N : ℕ} {ψ : Wavefunction (N+1)}
    (ha : IsAntisymmetric ψ) (W : Position → ℝ)
    (hi : ∀ σ i,Integrable (fun x : Configuration (N+1) => W (x i)*‖ψ σ x‖^2)) :
    rawExpectation ψ (fun x => ∑ i : Fin (N+1),W (x i))=∫ z,W z*density ψ z := by
  have hii (i : Fin (N+1)) : Integrable (fun x => W (x i)*configurationDensity ψ x) := by
    simp only [configurationDensity,Finset.mul_sum]
    exact integrable_finsetSum _ (fun σ _ => hi σ i)
  calc
    _=∑ i : Fin (N+1),rawExpectation ψ (fun x => W (x i)) := by
      unfold rawExpectation
      simp_rw [Finset.sum_mul]
      exact integral_finsetSum _ (fun i _ => hii i)
    _=∑ _i : Fin (N+1),rawExpectation ψ (fun x => W (x 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      simpa only [Function.comp_apply,Equiv.swap_apply_left] using
        rawExpectation_perm ha (Equiv.swap 0 i) (fun x => W (x 0))
    _=_ := by rw [density_weight_eq_first_site ψ W (fun σ => hi σ 0)]; simp

lemma fromH1_coulomb_weight_integrable {n : ℕ} (u : Coulomb.H1Vector n)
    (y : Position) (σ : Spins n) (i : Fin n) :
    Integrable (fun x : Configuration n => coulombKernel (y-x i)*‖fromH1Wave u σ x‖^2) := by
  have H := (flattenConfiguration_measurePreserving n).integrable_comp_of_integrable
    (u.nuclear_coulomb_integrable_bound σ i y (by norm_num : (0:ℝ)<1)).1
  change Integrable (fun x : Configuration n => Coulomb.coulombKernel (x i-y)*‖fromH1Wave u σ x‖^2) at H
  simpa only [coulombKernel,Coulomb.coulombKernel,norm_sub_rev] using H

lemma fromH1_coulomb_near_weight_integrable {n : ℕ} (u : Coulomb.H1Vector n)
    (y : Position) (R : ℝ) (σ : Spins n) (i : Fin n) :
    Integrable (fun x : Configuration n => (Metric.closedBall y R).indicator
      (fun z => coulombKernel (y-z)) (x i)*‖fromH1Wave u σ x‖^2) := by
  have H := (fromH1_coulomb_weight_integrable u y σ i).indicator
    ((measurableSet_closedBall : MeasurableSet (Metric.closedBall y R)).preimage (measurable_pi_apply i))
  apply H.congr
  exact Eventually.of_forall fun x => by
    by_cases hx : x i∈Metric.closedBall y R <;> simp [hx]

lemma rawLaw_no_fixed_particle {N : ℕ} {ψ : Wavefunction (N+1)}
    (ha : IsAntisymmetric ψ) (hψ : ∀ σ,MemLp (ψ σ) 2 volume)
    (hn : normSquared ψ=1) (y : Position) :
    ∀ᵐ x ∂rawLaw ψ,∀ i : Fin (N+1),x i≠y := by
  have := rawLaw_isProbability hψ hn
  have hi := (rawCount_memLp hψ hn (hS := measurableSet_singleton y)).integrable (by norm_num)
  have hz : (∫ x,rawCount {y} x ∂rawLaw ψ)=0 := by
    rw [integral_rawLaw hψ,rawExpectation_count_eq_density ha hψ (measurableSet_singleton y)]
    exact setIntegral_measure_zero _ (measure_singleton y)
  have he : rawCount (n := N+1) {y}=ᵐ[rawLaw ψ] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall (rawCount_nonneg {y})) hi).mp hz
  filter_upwards [he] with x hx
  intro i hiy
  have hb := Finset.single_le_sum (fun j _ => show 0≤({y}:Set Position).indicator (fun _ => (1:ℝ)) (x j) from by
    by_cases hj : x j=y <;> simp [hj]) (Finset.mem_univ i)
  change ({y}:Set Position).indicator (fun _ => (1:ℝ)) (x i)≤rawCount {y} x at hb
  simp [hiy,hx] at hb
  norm_num at hb
end NeutralAtom
end

end
end

end OAI
