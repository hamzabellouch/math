import Mathlib
import OAI.Analysis.CoulombIonization.FormDomain.CoreKinetic
import OAI.Analysis.CoulombIonization.FormDomain.CoreSliceMassIntegrable
import OAI.Analysis.CoulombIonization.FieldAnalysis.WeightedAverage

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Filter
open scoped BigOperators

namespace CoulombNeumann
open CoulombAtom
variable {N : ℕ}

lemma retainedPressure_value_integrable {ψ : FormVector N} (hψ : SobolevFermion ψ)
    {b : ℝ} (hb : 0 < b) (S : Configuration N → Finset (Fin N))
    (hS : ∀ i, MeasurableSet {x | i ∈ S x}) (s : Spins N) :
    Integrable (fun x => retainedPressure b (S x) x*‖ψ.value s x‖^2) := by
  apply (hψ.1 s).norm.integrable_sq.bdd_mul
    (retainedPressure_measurable b S hS).aestronglyMeasurable
  exact Eventually.of_forall (fun x => by
    change ‖retainedPressure b (S x) x‖ ≤ b⁻¹^2*(N:ℝ)^(5/3:ℝ)
    rw [Real.norm_of_nonneg (retainedPressure_nonneg hb _ _)]
    exact (retainedPressure_le_average hb _ _).trans (physicalPressureAverage_le b x))

lemma physicalPressure_spin_integrable {ψ : FormVector N} (hψ : SobolevFermion ψ)
    {b : ℝ} (hb : 0 < b) (s : Spins N) :
    Integrable (fun x => physicalPressure b x*‖ψ.value s x‖^2) := by
  apply (hψ.1 s).norm.integrable_sq.bdd_mul (physicalPressure_measurable b).aestronglyMeasurable
  exact Eventually.of_forall (fun x => by
    change ‖physicalPressure b x‖ ≤ b⁻¹^2*(N:ℝ)^(5/3:ℝ)
    rw [Real.norm_of_nonneg (physicalPressure_nonneg hb _)]
    exact (physicalPressure_le_average hb _).trans (physicalPressureAverage_le b x))

end CoulombNeumann
namespace CoulombAtom
open CoulombNeumann
variable {N : ℕ}

theorem SobolevFermion.neumann_retained {ψ : FormVector N} (hψ : SobolevFermion ψ)
    {b : ℝ} (hb : 0 < b) (S : Spins N → Configuration N → Finset (Fin N))
    (hS : ∀ s i, MeasurableSet {x | i ∈ S s x}) :
    tfKinetic*(∑ s, ∫ x, retainedPressure b (S s x) x*‖ψ.value s x‖^2) ≤ formKinetic ψ+
      b⁻¹^2*neumannRemainderConstant*((N:ℝ)^(4/3:ℝ)+(N:ℝ))*formMass ψ := by
  apply le_trans _ (hψ.neumann_radial_smear hb)
  apply mul_le_mul_of_nonneg_left _ (by unfold tfKinetic; positivity)
  unfold formDensity
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun s _ => physicalPressure_spin_integrable hψ hb s)]
  apply Finset.sum_le_sum
  intro s _
  exact integral_mono (retainedPressure_value_integrable hψ hb (S s) (hS s) s)
    (physicalPressure_spin_integrable hψ hb s)
    (fun x => mul_le_mul_of_nonneg_right (retainedPressure_le_full hb _ _) (sq_nonneg _))

theorem FormAdmissible.neumann_retained {ψ : FormVector N} (hψ : FormAdmissible ψ)
    {b : ℝ} (hb : 0 < b) (S : Spins N → Configuration N → Finset (Fin N))
    (hS : ∀ s i, MeasurableSet {x | i ∈ S s x}) :
    tfKinetic*(∑ s, ∫ x, retainedPressure b (S s x) x*‖ψ.value s x‖^2) ≤ formKinetic ψ+
      b⁻¹^2*neumannRemainderConstant*((N:ℝ)^(4/3:ℝ)+(N:ℝ)) := by
  have hh := hψ.sobolevFermion.neumann_retained hb S hS
  unfold formMass at hh
  simpa only [hψ.2.2.2.2.1,mul_one] using hh

end CoulombAtom

open MeasureTheory Set Filter
open scoped BigOperators

namespace CoulombNeumann
open CoulombAtom
variable {N M : ℕ}

lemma retained_slice_pressure_integrable {ψ : FormVector (N+M)} (hψ : SobolevVector ψ)
    {b : ℝ} (hb : 0 < b) (S : Configuration N × Configuration M → Finset (Fin N))
    (hS : ∀ i, MeasurableSet {p | i ∈ S p}) (s : Spins N) (t : Spins M) :
    Integrable (fun y => ∫ x, retainedPressure b (S (x,y)) x*‖(coreSlice ψ t y).value s x‖^2) := by
  have hi := integrable_join (N := N) (M := M) (hψ.1 (joinLists s t)).norm.integrable_sq
  have hm := retainedPressure_measurable_param b S Prod.fst hS measurable_fst
  have hh : Integrable (fun p : Configuration N × Configuration M =>
      retainedPressure b (S p) p.1*‖ψ.value (joinLists s t) (joinLists p.1 p.2)‖^2) := by
    apply hi.bdd_mul hm.aestronglyMeasurable
    exact Eventually.of_forall (fun p => by
      change ‖retainedPressure b (S p) p.1‖ ≤ b⁻¹^2*(N:ℝ)^(5/3:ℝ)
      rw [Real.norm_of_nonneg (retainedPressure_nonneg hb _ _)]
      exact (retainedPressure_le_average hb _ _).trans (physicalPressureAverage_le b p.1))
  exact hh.integral_prod_right

lemma retained_slice_pressure_sum_integrable {ψ : FormVector (N+M)} (hψ : SobolevVector ψ)
    {b : ℝ} (hb : 0 < b) (S : Spins N → Configuration N × Configuration M → Finset (Fin N))
    (hS : ∀ s i, MeasurableSet {p | i ∈ S s p}) (t : Spins M) :
    Integrable (fun y => ∑ s, ∫ x, retainedPressure b (S s (x,y)) x*‖(coreSlice ψ t y).value s x‖^2) :=
  integrable_finsetSum _ (fun s _ => retained_slice_pressure_integrable hψ hb (S s) (hS s) s t)

lemma retained_section_measurable (S : Configuration N × Configuration M → Finset (Fin N))
    (hS : ∀ i, MeasurableSet {p | i ∈ S p}) (y : Configuration M) (i : Fin N) :
    MeasurableSet {x | i ∈ S (x,y)} :=
  (measurable_id.prodMk measurable_const) (hS i)

end CoulombNeumann
namespace CoulombAtom
open CoulombNeumann
variable {N M : ℕ}

theorem CoreAntisymmetric.neumann_retained_slices {ψ : FormVector (N+M)}
    (ha : CoreAntisymmetric ψ) (hψ : SobolevVector ψ) {b : ℝ} (hb : 0 < b)
    (S : Spins M → Spins N → Configuration N × Configuration M → Finset (Fin N))
    (hS : ∀ t s i, MeasurableSet {p | i ∈ S t s p}) :
    tfKinetic*(∑ t : Spins M, ∫ y, ∑ s, ∫ x,
      retainedPressure b (S t s (x,y)) x*‖(coreSlice ψ t y).value s x‖^2) ≤
      coreKinetic ψ+b⁻¹^2*neumannRemainderConstant*((N:ℝ)^(4/3:ℝ)+(N:ℝ))*formMass ψ := by
  have ht (t : Spins M) :
      tfKinetic*(∫ y, ∑ s, ∫ x, retainedPressure b (S t s (x,y)) x*
        ‖(coreSlice ψ t y).value s x‖^2) ≤
      (∫ y, formKinetic (coreSlice ψ t y))+
        b⁻¹^2*neumannRemainderConstant*((N:ℝ)^(4/3:ℝ)+(N:ℝ))*(∫ y, formMass (coreSlice ψ t y)) := by
    rw [←integral_const_mul,←integral_const_mul,
      ←integral_add (coreSlice_parts_integrable hψ t).1 ((hψ.coreSlice_mass_integrable t).const_mul _)]
    apply integral_mono_ae ((retained_slice_pressure_sum_integrable hψ hb (S t) (hS t) t).const_mul _)
      ((coreSlice_parts_integrable hψ t).1.add ((hψ.coreSlice_mass_integrable t).const_mul _))
    filter_upwards [ha.ae_coreSlice hψ t] with y hy
    exact hy.neumann_retained hb (fun s x => S t s (x,y))
      (fun s i => retained_section_measurable (S t s) (hS t s) y i)
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun t _ => ht t)
  simpa only [Finset.sum_add_distrib,←Finset.mul_sum,integral_core_kinetic hψ,
    hψ.integral_coreSlice_mass] using hh

end CoulombAtom

open MeasureTheory Set Filter
open scoped BigOperators

namespace CoulombNeumann
open CoulombAtom
variable {N M : ℕ}

lemma pointRepulsion_join_integrable {ψ : FormVector (N+M)} (hψ : SobolevVector ψ)
    (s : Spins N) (t : Spins M) :
    Integrable (fun p : Configuration N × Configuration M =>
      pointRepulsion p.1*‖ψ.value (joinLists s t) (joinLists p.1 p.2)‖^2) := by
  simp_rw [pointRepulsion_mul]
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  split_ifs with hij
  · have hne : (finSumFinEquiv (Sum.inl i) : Fin (N+M)) ≠ finSumFinEquiv (Sum.inl j) :=
      fun hh => (ne_of_lt hij) (Sum.inl.inj (finSumFinEquiv.injective hh))
    have hh := integrable_join (N := N) (M := M)
      (hψ.pair_integrable (joinLists s t) _ _ hne)
    simpa only [joinLists_left] using hh
  · exact integrable_zero _ _ _

lemma retained_slice_direct_integrable {ψ : FormVector (N+M)} (hψ : SobolevVector ψ)
    {b : ℝ} (hb : 0 < b) (S : Configuration N × Configuration M → Finset (Fin N))
    (hS : ∀ i, MeasurableSet {p | i ∈ S p}) (s : Spins N) (t : Spins M) :
    Integrable (fun y => ∫ x, retainedDirect b (S (x,y)) x*‖(coreSlice ψ t y).value s x‖^2) := by
  have hi := integrable_join (N := N) (M := M) (hψ.1 (joinLists s t)).norm.integrable_sq
  have hm := retainedDirect_measurable_param b S Prod.fst hS measurable_fst
  have hh : Integrable (fun p : Configuration N × Configuration M =>
      retainedDirect b (S p) p.1*‖ψ.value (joinLists s t) (joinLists p.1 p.2)‖^2) := by
    apply ((pointRepulsion_join_integrable hψ s t).add
      (hi.const_mul (((2*Real.pi+1)/2)*(N:ℝ)/b))).mono'
      (hm.aestronglyMeasurable.mul hi.aestronglyMeasurable)
    have hn : ∀ᵐ p : Configuration N × Configuration M, Function.Injective p.1 := by
      rw [Measure.volume_eq_prod]
      exact Measure.quasiMeasurePreserving_fst.ae ((configuration_ae_nonsingular N).mono (fun _ h => h.2))
    filter_upwards [hn] with p hp
    change ‖retainedDirect b (S p) p.1*‖ψ.value (joinLists s t) (joinLists p.1 p.2)‖^2‖ ≤
      pointRepulsion p.1*‖ψ.value (joinLists s t) (joinLists p.1 p.2)‖^2+
        (((2*Real.pi+1)/2)*(N:ℝ)/b)*‖ψ.value (joinLists s t) (joinLists p.1 p.2)‖^2
    rw [Real.norm_of_nonneg (mul_nonneg (retainedDirect_nonneg hb _ _) (sq_nonneg _)),←add_mul]
    have hh := retained_physical_coulomb_lower hb (S p) p.1 hp
    change retainedDirect b (S p) p.1-_ ≤ pointRepulsion p.1 at hh
    exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  exact hh.integral_prod_right

lemma retained_slice_direct_sum_integrable {ψ : FormVector (N+M)} (hψ : SobolevVector ψ)
    {b : ℝ} (hb : 0 < b) (S : Spins N → Configuration N × Configuration M → Finset (Fin N))
    (hS : ∀ s i, MeasurableSet {p | i ∈ S s p}) (t : Spins M) :
    Integrable (fun y => ∑ s, ∫ x, retainedDirect b (S s (x,y)) x*‖(coreSlice ψ t y).value s x‖^2) :=
  integrable_finsetSum _ (fun s _ => retained_slice_direct_integrable hψ hb (S s) (hS s) s t)

end CoulombNeumann
namespace CoulombAtom
open CoulombNeumann
variable {N M : ℕ}

theorem CoreAntisymmetric.retained_repulsion_slices {ψ : FormVector (N+M)}
    (ha : CoreAntisymmetric ψ) (hψ : SobolevVector ψ) {b : ℝ} (hb : 0 < b)
    (S : Spins M → Spins N → Configuration N × Configuration M → Finset (Fin N))
    (hS : ∀ t s i, MeasurableSet {p | i ∈ S t s p}) :
    (∑ t : Spins M, ∫ y, ∑ s, ∫ x,
      retainedDirect b (S t s (x,y)) x*‖(coreSlice ψ t y).value s x‖^2) ≤
      coreRepulsion ψ+(((2*Real.pi+1)/2)*(N:ℝ)/b)*formMass ψ := by
  have ht (t : Spins M) :
      (∫ y, ∑ s, ∫ x, retainedDirect b (S t s (x,y)) x*
        ‖(coreSlice ψ t y).value s x‖^2) ≤
      (∫ y, formRepulsion (coreSlice ψ t y))+
        (((2*Real.pi+1)/2)*(N:ℝ)/b)*(∫ y, formMass (coreSlice ψ t y)) := by
    rw [←integral_const_mul,
      ←integral_add (coreSlice_parts_integrable hψ t).2.2 ((hψ.coreSlice_mass_integrable t).const_mul _)]
    apply integral_mono_ae (retained_slice_direct_sum_integrable hψ hb (S t) (hS t) t)
      ((coreSlice_parts_integrable hψ t).2.2.add ((hψ.coreSlice_mass_integrable t).const_mul _))
    filter_upwards [ha.ae_coreSlice hψ t] with y hy
    exact hy.retained_repulsion hb (fun s x => S t s (x,y))
      (fun s i => retained_section_measurable (S t s) (hS t s) y i)
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun t _ => ht t)
  simpa only [Finset.sum_add_distrib,←Finset.mul_sum,integral_core_repulsion hψ,
    hψ.integral_coreSlice_mass] using hh

end CoulombAtom

end

end OAI
