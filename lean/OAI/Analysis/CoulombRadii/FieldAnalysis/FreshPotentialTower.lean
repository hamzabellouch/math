import Mathlib
import OAI.Analysis.CoulombRadii.RandomFields.RecordedEnsemble

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
noncomputable section
namespace Coulomb

lemma potentialForm_min_tendsto {n : ℕ} (u : H1Vector n)
    (W : Configuration n → ℝ) (hW : Measurable W) (hW0 : ∀ x,0≤W x)
    (hi : ∀ s,Integrable (fun x => W x*‖u.value s x‖^2)) :
    Tendsto (fun k : ℕ => potentialForm (fun x => min (W x) (k:ℝ)) u)
      atTop (𝓝 (potentialForm W u)) := by
  apply tendsto_finsetSum
  intro s _
  apply tendsto_integral_of_dominated_convergence (fun x => W x*‖u.value s x‖^2)
  · intro k
    exact (hW.min measurable_const).aestronglyMeasurable.mul ((u.value_L2 s).aestronglyMeasurable.norm.pow 2)
  · exact hi s
  · intro k
    filter_upwards [] with x
    rw [Real.norm_of_nonneg (mul_nonneg (le_min (hW0 x) (Nat.cast_nonneg k)) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)
  · filter_upwards [] with x
    apply Tendsto.congr' _ tendsto_const_nhds
    have he : ∀ᶠ k : ℕ in atTop, W x≤(k:ℝ) :=
      tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (W x))
    exact he.mono (fun k hk => by dsimp only; rw [min_eq_left hk])

namespace RecordedEnsemble
lemma Conserves.nonnegative_observable {n : ℕ} {T : RecordedEnsemble n}
    {u : H1Vector n} (hT : T.Conserves u) (W : Configuration n → ℝ)
    (hW : Measurable W) (hW0 : ∀ x,0≤W x)
    (hi : ∀ s,Integrable (fun x => W x*‖u.value s x‖^2))
    (hTi : ∀ p s,Integrable (fun x => W (reindexConfiguration (T.labels p) x)*‖(T.vector p).value s x‖^2)) :
    (∑ p,potentialForm (W ∘ reindexConfiguration (T.labels p)) (T.vector p))=potentialForm W u := by
  have hleft : Tendsto (fun k : ℕ => ∑ p,potentialForm
      ((fun x => min (W x) (k:ℝ)) ∘ reindexConfiguration (T.labels p)) (T.vector p)) atTop
      (𝓝 (∑ p,potentialForm (W ∘ reindexConfiguration (T.labels p)) (T.vector p))) := by
    apply tendsto_finsetSum
    intro p _
    exact potentialForm_min_tendsto (T.vector p) _
      (hW.comp (reindexConfiguration_measurePreserving _).measurable) (fun x => hW0 _) (hTi p)
  have he (k : ℕ) : (∑ p,potentialForm
      ((fun x => min (W x) (k:ℝ)) ∘ reindexConfiguration (T.labels p)) (T.vector p))=
      potentialForm (fun x => min (W x) (k:ℝ)) u := by
    apply hT _ (hW.min measurable_const)
    exact ⟨k,fun x => by rw [abs_of_nonneg (le_min (hW0 x) (Nat.cast_nonneg k))]; exact min_le_right _ _⟩
  simp_rw [he] at hleft
  exact tendsto_nhds_unique hleft (potentialForm_min_tendsto u W hW hW0 hi)
end RecordedEnsemble

lemma nuclearPotential_reindex_labels {M m n : ℕ} (S : Nuclei M)
    (e : Fin m ≃ Fin n) (x : Configuration m) : nuclearPotential S (reindexConfiguration e x)=nuclearPotential S x := by
  unfold nuclearPotential
  exact (Equiv.sum_comp e (fun i => attraction S (position (reindexConfiguration e x) i))).symm.trans
    (Finset.sum_congr rfl (fun i _ => by rw [position_reindex]))

theorem RecordedEnsemble.Conserves.coulomb_potential {n : ℕ} {T : RecordedEnsemble n}
    {u : H1Vector n} (hT : T.Conserves u) (y : Space) :
    (∑ p,coreCoulombPotential (T.vector p) y)=coreCoulombPotential u y := by
  have hm : Measurable (nuclearPotential (n := n) (unitNucleus y)) :=
    Finset.measurable_sum _ (fun i _ => (attraction_measurable _).comp (positionCLM i).measurable)
  have hi := hT.nonnegative_observable (nuclearPotential (unitNucleus y)) hm
    (fun x => Finset.sum_nonneg (fun i _ => attraction_nonneg _ _))
    (u.nuclear_integrable (unitNucleus y)) (fun p s => by
      change Integrable (fun x : Configuration (T.out p+T.core p) => nuclearPotential (unitNucleus y) (reindexConfiguration (T.labels p) x)*‖(T.vector p).value s x‖^2)
      simp_rw [nuclearPotential_reindex_labels]
      exact (T.vector p).nuclear_integrable (unitNucleus y) s)
  simp only [Function.comp_def,nuclearPotential_reindex_labels] at hi
  change (∑ p,nuclearEnergy (unitNucleus y) (T.vector p))=nuclearEnergy (unitNucleus y) u at hi
  simpa only [nuclearEnergy_unit_eq_coreCoulomb] using hi

theorem fresh_core_coulomb_tower {m k : ℕ} (u : H1Vector (m+k)) (y : Space) :
    sliceExpectation u (fun s x => coreCoulombPotential (u.coreSlice s x).normalized y+
      nuclearPotential (unitNucleus y) x)=coreCoulombPotential u y := by
  have hc (s : Spins m) : Integrable (fun x => mass (u.coreSlice s x)*
      coreCoulombPotential (u.coreSlice s x).normalized y) := by
    simp only [←nuclearEnergy_unit_eq_coreCoulomb]
    change Integrable (fun x => mass (u.coreSlice s x)*potentialForm (nuclearPotential (unitNucleus y))
      (u.coreSlice s x).normalized)
    simp_rw [potentialForm_normalized_weight]
    exact potentialForm_coreSlice_integrable u s _ (fun t => u.core_nuclear_integrable (unitNucleus y) (Fin.append s t))
  have ho (s : Spins m) : Integrable (fun x => mass (u.coreSlice s x)*nuclearPotential (unitNucleus y) x) :=
    slice_weight_integrable_const u _ (u.outer_nuclear_integrable (unitNucleus y)) s
  rw [sliceExpectation_add u _ _ hc ho,sliceExpectation_const u _ (u.outer_nuclear_integrable (unitNucleus y))]
  have HH := conditional_core_nuclear_identity (unitNucleus y) u
  simp only [nuclearEnergy_unit_eq_coreCoulomb] at HH
  change sliceExpectation u (fun s x => coreCoulombPotential (u.coreSlice s x).normalized y)=_ at HH
  rw [HH,←nuclearEnergy_unit_eq_coreCoulomb,nuclearEnergy_split]
  change potentialForm _ u+potentialForm _ u=potentialForm _ u+potentialForm _ u
  ring

theorem RecordedEnsemble.Conserves.fresh_coulomb_tower {n : ℕ} {T : RecordedEnsemble n}
    {u : H1Vector n} (hT : T.Conserves u) (y : Space) :
    (∑ p,sliceExpectation (T.vector p) (fun s x =>
      coreCoulombPotential ((T.vector p).coreSlice s x).normalized y+
      nuclearPotential (unitNucleus y) x))=coreCoulombPotential u y := by
  simp_rw [fresh_core_coulomb_tower]
  exact hT.coulomb_potential y
end Coulomb
end

end
end

end OAI
