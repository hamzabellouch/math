import Mathlib
import OAI.Analysis.CoulombRadii.Screening.CoreScreenedField
import OAI.Analysis.CoulombRadii.RandomFields.ConditionalEnergy

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set
open scoped BigOperators Matrix ENNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb

lemma nuclearEnergy_unit_eq_coreCoulomb {k : ℕ} (u : H1Vector k) (a : Space) :
    nuclearEnergy (unitNucleus a) u = coreCoulombPotential u a := by
  unfold nuclearEnergy coreCoulombPotential
  apply Finset.sum_congr rfl
  intro s _
  simp only [attraction_unitNucleus, Finset.sum_mul]
  exact integral_finsetSum _ (fun i _ =>
    (u.nuclear_coulomb_integrable_bound s i a (by norm_num : (0:ℝ)<1)).1)

lemma potentialForm_cross_eq_coreCoulomb {m k : ℕ} (x : Configuration m) (u : H1Vector k) :
    potentialForm (crossPotential x) u = ∑ i : Fin m, coreCoulombPotential u (position x i) := by
  change (∑ t : Spins k, ∫ y, crossPotential x y*‖u.value t y‖^2) = _
  rw [crossPotential_spin_integral]
  exact Finset.sum_congr rfl (fun i _ => nuclearEnergy_unit_eq_coreCoulomb u (position x i))

lemma conditionalEnergy_eq_screened {M m k : ℕ} (S : Nuclei M) (ψ : H1Vector (m+k))
    (s : Spins m) (x : Configuration m) :
    conditionalEnergy S ψ s x = form S (ψ.coreSlice s x).normalized -
      (∑ i : Fin m, coreScreenedField S (ψ.coreSlice s x).normalized (position x i)) + pairPotential x := by
  rw [conditionalEnergy, potentialForm_cross_eq_coreCoulomb]
  simp only [coreScreenedField, Finset.sum_sub_distrib, nuclearPotential]
  ring

def sliceExpectation {m k : ℕ} (ψ : H1Vector (m+k)) (f : Spins m → Configuration m → ℝ) : ℝ :=
  ∑ s : Spins m, ∫ x, mass (ψ.coreSlice s x)*f s x

lemma slice_weight_integrable_const {m k : ℕ} (ψ : H1Vector (m+k))
    (f : Configuration m → ℝ)
    (hf : ∀ st, Integrable (fun z => f ((joinConfiguration m k).symm z).1*‖ψ.value st z‖^2))
    (s : Spins m) : Integrable (fun x => mass (ψ.coreSlice s x)*f x) := by
  have H := potentialForm_coreSlice_parameter_integrable ψ s (fun x _ => f x) (fun t => hf (Fin.append s t))
  apply H.congr
  exact Eventually.of_forall (fun x => by dsimp only; rw [potentialForm_const]; ring)

lemma sliceExpectation_const {m k : ℕ} (ψ : H1Vector (m+k))
    (f : Configuration m → ℝ)
    (hf : ∀ st, Integrable (fun z => f ((joinConfiguration m k).symm z).1*‖ψ.value st z‖^2)) :
    sliceExpectation ψ (fun _ x => f x) = potentialForm (fun z => f ((joinConfiguration m k).symm z).1) ψ := by
  unfold sliceExpectation
  simp_rw [mul_comm (mass _) (f _), ←potentialForm_const]
  exact integral_potentialForm_coreSlice_parameter ψ (fun x _ => f x) hf

lemma measurable_retained_sum {α : Type*} [MeasurableSpace α] {n : ℕ}
    (r : α → Finset (Fin n)) (hr : ∀ i, MeasurableSet {x | i ∈ r x})
    (f : Fin n → α → ℝ) (hf : ∀ i, Measurable (f i)) :
    Measurable (fun x => ∑ i ∈ r x, f i x) := by
  have he (x : α) : (∑ i ∈ r x, f i x) = ∑ i : Fin n, if i ∈ r x then f i x else 0 := by simp
  simp_rw [he]
  exact Finset.measurable_sum _ (fun i _ => Measurable.ite (hr i) (hf i) measurable_const)

def retainedNuclearPotential {M m : ℕ} (S : Nuclei M)
    (r : Configuration m → Finset (Fin m)) (x : Configuration m) : ℝ :=
  ∑ i ∈ r x, attraction S (position x i)

def retainedCrossPotential {m k : ℕ} (r : Configuration m → Finset (Fin m))
    (x : Configuration m) (y : Configuration k) : ℝ :=
  ∑ i ∈ r x, ∑ j : Fin k, coulombKernel (position x i-position y j)

lemma retainedNuclearPotential_nonneg {M m : ℕ} (S : Nuclei M)
    (r : Configuration m → Finset (Fin m)) (x : Configuration m) :
    0 ≤ retainedNuclearPotential S r x := Finset.sum_nonneg (fun i _ => attraction_nonneg S (position x i))
lemma retainedNuclearPotential_le {M m : ℕ} (S : Nuclei M)
    (r : Configuration m → Finset (Fin m)) (x : Configuration m) :
    retainedNuclearPotential S r x ≤ nuclearPotential S x :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => attraction_nonneg S (position x i))
lemma retainedNuclearPotential_measurable {M m : ℕ} (S : Nuclei M)
    (r : Configuration m → Finset (Fin m)) (hr : ∀ i, MeasurableSet {x | i ∈ r x}) :
    Measurable (retainedNuclearPotential S r) :=
  measurable_retained_sum r hr _ (fun i => (attraction_measurable S).comp (positionCLM i).measurable)

lemma retainedCrossPotential_nonneg {m k : ℕ} (r : Configuration m → Finset (Fin m))
    (x : Configuration m) (y : Configuration k) : 0 ≤ retainedCrossPotential r x y :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => coulombKernel_nonneg _))
lemma retainedCrossPotential_le {m k : ℕ} (r : Configuration m → Finset (Fin m))
    (x : Configuration m) (y : Configuration k) : retainedCrossPotential r x y ≤ crossPotential x y :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun _ _ _ => Finset.sum_nonneg (fun _ _ => coulombKernel_nonneg _))
lemma retainedCrossPotential_measurable {m k : ℕ} (r : Configuration m → Finset (Fin m))
    (hr : ∀ i, MeasurableSet {x | i ∈ r x}) :
    Measurable (fun p : Configuration m × Configuration k => retainedCrossPotential r p.1 p.2) := by
  unfold retainedCrossPotential
  apply measurable_retained_sum (fun p : Configuration m × Configuration k => r p.1)
    (fun i => (hr i).preimage measurable_fst)
  intro i
  apply Finset.measurable_sum
  intro j _
  exact coulombKernel_measurable.comp (((positionCLM i).measurable.comp measurable_fst).sub
    ((positionCLM j).measurable.comp measurable_snd))

lemma H1Vector.retained_outer_nuclear_integrable {M m k : ℕ} (ψ : H1Vector (m+k))
    (S : Nuclei M) (r : Configuration m → Finset (Fin m))
    (hr : ∀ i, MeasurableSet {x | i ∈ r x}) (st : Spins (m+k)) :
    Integrable (fun z => retainedNuclearPotential S r ((joinConfiguration m k).symm z).1*‖ψ.value st z‖^2) := by
  apply (ψ.outer_nuclear_integrable S st).mono'
  · exact ((retainedNuclearPotential_measurable S r hr).comp
      (measurable_fst.comp (joinConfiguration m k).symm.continuous.measurable)).aestronglyMeasurable.mul
        (((ψ.value_L2 st).integrable_norm_pow (p:=2) (by decide)).aestronglyMeasurable)
  · exact Eventually.of_forall fun z => by
      rw [Real.norm_of_nonneg (mul_nonneg (retainedNuclearPotential_nonneg ..) (sq_nonneg _))]
      exact mul_le_mul_of_nonneg_right (retainedNuclearPotential_le S r _) (sq_nonneg _)

lemma H1Vector.retained_cross_integrable {m k : ℕ} (ψ : H1Vector (m+k))
    (r : Configuration m → Finset (Fin m)) (hr : ∀ i, MeasurableSet {x | i ∈ r x}) (st : Spins (m+k)) :
    Integrable (fun z => retainedCrossPotential r ((joinConfiguration m k).symm z).1
      ((joinConfiguration m k).symm z).2*‖ψ.value st z‖^2) := by
  apply (ψ.cross_integrable st).mono'
  · exact ((retainedCrossPotential_measurable r hr).comp
      (joinConfiguration m k).symm.continuous.measurable).aestronglyMeasurable.mul
        (((ψ.value_L2 st).integrable_norm_pow (p:=2) (by decide)).aestronglyMeasurable)
  · exact Eventually.of_forall fun z => by
      rw [Real.norm_of_nonneg (mul_nonneg (retainedCrossPotential_nonneg ..) (sq_nonneg _))]
      exact mul_le_mul_of_nonneg_right (retainedCrossPotential_le r _ _) (sq_nonneg _)

lemma potentialForm_retainedCross_eq {m k : ℕ} (r : Configuration m → Finset (Fin m))
    (x : Configuration m) (u : H1Vector k) :
    potentialForm (retainedCrossPotential r x) u = ∑ i ∈ r x, coreCoulombPotential u (position x i) := by
  have he (y : Configuration k) : retainedCrossPotential r x y =
      ∑ i ∈ r x, nuclearPotential (unitNucleus (position x i)) y := by
    unfold retainedCrossPotential nuclearPotential
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [attraction_unitNucleus, coulombKernel_sub_comm]
  unfold potentialForm
  simp_rw [he, Finset.sum_mul]
  have hi (s : Spins k) :
      (∫ y, ∑ i ∈ r x, nuclearPotential (unitNucleus (position x i)) y*‖u.value s y‖^2) =
      ∑ i ∈ r x, ∫ y, nuclearPotential (unitNucleus (position x i)) y*‖u.value s y‖^2 :=
    integral_finsetSum _ (fun i _ => u.nuclear_integrable (unitNucleus (position x i)) s)
  simp_rw [hi]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun i _ => nuclearEnergy_unit_eq_coreCoulomb u (position x i))

lemma retained_field_weight {M m k : ℕ} (S : Nuclei M) (ψ : H1Vector (m+k))
    (r : Configuration m → Finset (Fin m)) (s : Spins m) (x : Configuration m) :
    mass (ψ.coreSlice s x)*(∑ i ∈ r x, coreScreenedField S (ψ.coreSlice s x).normalized (position x i)) =
      mass (ψ.coreSlice s x)*retainedNuclearPotential S r x -
        potentialForm (retainedCrossPotential r x) (ψ.coreSlice s x) := by
  simp only [coreScreenedField, Finset.sum_sub_distrib, mul_sub]
  rw [←potentialForm_retainedCross_eq, potentialForm_normalized_weight]
  rfl

lemma retained_field_weight_integrable {M m k : ℕ} (S : Nuclei M) (ψ : H1Vector (m+k))
    (r : Configuration m → Finset (Fin m)) (hr : ∀ i, MeasurableSet {x | i ∈ r x}) (s : Spins m) :
    Integrable (fun x => mass (ψ.coreSlice s x)*
      (∑ i ∈ r x, coreScreenedField S (ψ.coreSlice s x).normalized (position x i))) := by
  simp_rw [retained_field_weight]
  exact (slice_weight_integrable_const ψ _ (ψ.retained_outer_nuclear_integrable S r hr) s).sub
    (potentialForm_coreSlice_parameter_integrable ψ s (retainedCrossPotential r)
      (fun t => ψ.retained_cross_integrable r hr (Fin.append s t)))

end Coulomb

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical

end

end OAI
