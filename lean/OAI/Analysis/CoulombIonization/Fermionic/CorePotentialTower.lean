import Mathlib
import OAI.Analysis.CoulombIonization.FormDomain.FormRawPotential

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set
open scoped BigOperators

namespace CoulombAtom

lemma rawPotential_weighted_integrable {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevVector ψ) (s : Spins N) (y : Space) :
    Integrable (fun x => rawPotential y x*‖ψ.value s x‖^2) := by
  simp only [rawPotential,Finset.sum_mul]
  apply integrable_finsetSum
  intro i _
  simpa only [one_div,mul_comm,←div_eq_mul_inv] using hψ.shifted_nuclear_integrable s i y

lemma integral_rawPotential_formRawLaw {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevVector ψ) (y : Space) :
    (∫ x, rawPotential y x ∂formRawLaw ψ) = coreCoulombAt ψ y := by
  rw [formRawLaw_integral hψ]
  simp only [formRawDensity,Finset.sum_mul]
  rw [integral_finsetSum _ (fun s _ => by
    simpa only [mul_comm] using rawPotential_weighted_integrable hψ s y)]
  unfold coreCoulombAt
  congr 1
  ext s
  simp only [rawPotential,Finset.mul_sum,mul_one_div]
  exact integral_finsetSum _ (fun i _ => hψ.shifted_nuclear_integrable s i y)

lemma coreSlice_coreCoulombAt_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (t : Spins M) (y : Space) :
    Integrable (fun u : Configuration M => coreCoulombAt (coreSlice ψ t u) y) := by
  unfold coreCoulombAt
  apply integrable_finsetSum
  intro s _
  apply integrable_finsetSum
  intro i _
  have hh := (integrable_join (N := N) (M := M)
    (hψ.shifted_nuclear_integrable (joinLists s t) (finSumFinEquiv (Sum.inl i)) y)).integral_prod_right
  simpa only [coreSlice,joinLists_left] using hh

lemma rawPotential_coreSlice_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (t : Spins M) (y : Space) :
    Integrable (fun u : Configuration M => rawPotential y u*formMass (coreSlice ψ t u)) := by
  simp only [rawPotential,Finset.sum_mul]
  apply integrable_finsetSum
  intro i _
  simpa only [one_div,mul_comm,←div_eq_mul_inv] using coreSlice_mass_shifted_integrable hψ t i y

lemma integral_coreSlice_coreCoulombAt {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (y : Space) :
    (∑ t : Spins M, ∫ u : Configuration M, coreCoulombAt (coreSlice ψ t u) y) =
      ∑ s : Spins (N+M), ∑ i : Fin N, ∫ x, ‖ψ.value s x‖^2/‖x (finSumFinEquiv (Sum.inl i))-y‖ := by
  have hi (s : Spins N) (t : Spins M) (i : Fin N) : Integrable (fun u : Configuration M =>
      ∫ v : Configuration N, ‖ψ.value (joinLists s t) (joinLists v u)‖^2/‖v i-y‖) := by
    simpa only [joinLists_left] using (integrable_join (N := N) (M := M)
      (hψ.shifted_nuclear_integrable (joinLists s t) (finSumFinEquiv (Sum.inl i)) y)).integral_prod_right
  simp only [coreCoulombAt,coreSlice]
  simp_rw [integral_finsetSum _ (fun s _ => integrable_finsetSum _ (fun i _ => hi s _ i)),
    integral_finsetSum _ (fun i _ => hi _ _ i)]
  have he (s : Spins N) (t : Spins M) (i : Fin N) :
      (∫ u : Configuration M, ∫ v : Configuration N,
        ‖ψ.value (joinLists s t) (joinLists v u)‖^2/‖v i-y‖) =
      ∫ x, ‖ψ.value (joinLists s t) x‖^2/‖x (finSumFinEquiv (Sum.inl i))-y‖ := by
    simpa only [joinLists_left] using integral_join (N := N) (M := M)
      (hψ.shifted_nuclear_integrable (joinLists s t) (finSumFinEquiv (Sum.inl i)) y)
  simp_rw [he]
  exact sum_spin_join (fun s : Spins (N+M) => ∑ i : Fin N,
    ∫ x, ‖ψ.value s x‖^2/‖x (finSumFinEquiv (Sum.inl i))-y‖)

lemma integral_rawPotential_coreSlice {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (y : Space) :
    (∑ t : Spins M, ∫ u : Configuration M, rawPotential y u*formMass (coreSlice ψ t u)) =
      ∑ s : Spins (N+M), ∑ i : Fin M, ∫ x, ‖ψ.value s x‖^2/‖x (finSumFinEquiv (Sum.inr i))-y‖ := by
  have hi (s : Spins (N+M)) : Integrable (fun x =>
      rawPotential y (outProjection x)*‖ψ.value s x‖^2) := by
    simp only [rawPotential,Finset.sum_mul,outProjection]
    apply integrable_finsetSum
    intro i _
    simpa only [one_div,mul_comm,←div_eq_mul_inv] using
      hψ.shifted_nuclear_integrable s (finSumFinEquiv (Sum.inr i)) y
  rw [weighted_coreSlice_eq_full_integrable _ _ hi]
  apply Finset.sum_congr rfl
  intro s _
  simp only [rawPotential,outProjection]
  simp only [Finset.sum_mul,div_mul_eq_mul_div,one_mul]
  exact integral_finsetSum _ (fun i _ => hψ.shifted_nuclear_integrable s (finSumFinEquiv (Sum.inr i)) y)

lemma fresh_core_outer_potential_tower {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (y : Space) :
    (∑ t : Spins M, ∫ u : Configuration M,
      coreCoulombAt (coreSlice ψ t u) y+rawPotential y u*formMass (coreSlice ψ t u)) =
      coreCoulombAt ψ y := by
  simp_rw [integral_add (coreSlice_coreCoulombAt_integrable hψ _ y)
    (rawPotential_coreSlice_integrable hψ _ y)]
  rw [Finset.sum_add_distrib,integral_coreSlice_coreCoulombAt hψ y,
    integral_rawPotential_coreSlice hψ y,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  change (∑ i : Fin N, ∫ x, ‖ψ.value s x‖^2/‖x (finSumFinEquiv (Sum.inl i))-y‖) +
    (∑ i : Fin M, ∫ x, ‖ψ.value s x‖^2/‖x (finSumFinEquiv (Sum.inr i))-y‖) =
    ∑ i : Fin (N+M), ∫ x, ‖ψ.value s x‖^2/‖x i-y‖
  simpa only [Fintype.sum_sum_type] using
    (Equiv.sum_comp finSumFinEquiv (fun i : Fin (N+M) => ∫ x, ‖ψ.value s x‖^2/‖x i-y‖))

end CoulombAtom

end

end OAI
