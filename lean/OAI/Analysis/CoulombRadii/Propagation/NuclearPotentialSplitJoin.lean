import Mathlib
import OAI.Analysis.CoulombRadii.Propagation.NuclearPotential
import OAI.Analysis.CoulombRadii.FieldAnalysis.CorePerm

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
namespace Coulomb

lemma nuclearPotential_split_join {M m k : ℕ} (S : Nuclei M) (x : Configuration m)
    (y : Configuration k) :
    nuclearPotential S (joinConfiguration m k (x,y)) = nuclearPotential S x + nuclearPotential S y := by
  simp only [nuclearPotential, Fin.sum_univ_add, position_join_left, position_join_right]

lemma pairPotential_split_join {m k : ℕ} (x : Configuration m) (y : Configuration k) :
    pairPotential (joinConfiguration m k (x,y)) = pairPotential x + pairPotential y +
      ∑ i : Fin m, ∑ j : Fin k, coulombKernel (position x i - position y j) := by
  simp only [pairPotential, Fin.sum_univ_add, position_join_left, position_join_right]
  have hleft (i j : Fin m) : Fin.castAdd k i < Fin.castAdd k j ↔ i < j := by rfl
  have hright (i j : Fin k) : Fin.natAdd m i < Fin.natAdd m j ↔ i < j := by
    simp only [Fin.lt_def, Fin.val_natAdd, Nat.add_lt_add_iff_left]
  have hlr (i : Fin m) (j : Fin k) : Fin.castAdd k i < Fin.natAdd m j := by
    simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]; omega
  have hrl (i : Fin k) (j : Fin m) : ¬Fin.natAdd m i < Fin.castAdd k j := by
    simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]; omega
  simp only [hleft, hright, hlr, hrl, ite_true, ite_false, Finset.sum_const_zero, zero_add,
    Finset.sum_add_distrib]
  ring

lemma H1Vector.core_nuclear_integrable {M m k : ℕ} (ψ : H1Vector (m+k))
    (S : Nuclei M) (st : Spins (m+k)) :
    Integrable (fun z => nuclearPotential S ((joinConfiguration m k).symm z).2 * ‖ψ.value st z‖^2) := by
  simp only [nuclearPotential, attraction, position_split_right, Finset.sum_mul]
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  have H := (ψ.nuclear_coulomb_integrable_bound st (Fin.natAdd m i) (S.position j)
    (by norm_num : (0:ℝ)<1)).1
  simpa only [mul_assoc] using H.const_mul (S.charge j)

lemma H1Vector.core_pair_integrable {m k : ℕ} (ψ : H1Vector (m+k)) (st : Spins (m+k)) :
    Integrable (fun z => pairPotential ((joinConfiguration m k).symm z).2 * ‖ψ.value st z‖^2) := by
  simp only [pairPotential, position_split_right, Finset.sum_mul]
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  by_cases hij : i < j
  · simp only [ite_eq_left hij]
    exact (ψ.pair_coulomb_integrable_bound st (Fin.natAdd m i) (Fin.natAdd m j)
      (fun he => hij.ne (by apply Fin.ext; have hh := congrArg Fin.val he; simpa only [Fin.val_natAdd, Nat.add_left_cancel_iff] using hh)) (by norm_num : (0:ℝ)<1)).1
  · simp only [ite_eq_right hij, zero_mul]
    exact integrable_zero _ _ _

lemma conditional_core_nuclear_identity {M m k : ℕ} (S : Nuclei M) (ψ : H1Vector (m+k)) :
    (∑ s : Spins m, ∫ x, mass (ψ.coreSlice s x) * nuclearEnergy S (ψ.coreSlice s x).normalized) =
      ∑ st : Spins (m+k), ∫ z, nuclearPotential S ((joinConfiguration m k).symm z).2 * ‖ψ.value st z‖^2 := by
  change (∑ s : Spins m, ∫ x, mass (ψ.coreSlice s x) *
    potentialForm (nuclearPotential S) (ψ.coreSlice s x).normalized) = _
  simp_rw [potentialForm_normalized_weight]
  exact integral_potentialForm_coreSlice ψ (nuclearPotential S) (ψ.core_nuclear_integrable S)

lemma conditional_core_pair_identity {m k : ℕ} (ψ : H1Vector (m+k)) :
    (∑ s : Spins m, ∫ x, mass (ψ.coreSlice s x) * pairEnergy (ψ.coreSlice s x).normalized) =
      ∑ st : Spins (m+k), ∫ z, pairPotential ((joinConfiguration m k).symm z).2 * ‖ψ.value st z‖^2 := by
  change (∑ s : Spins m, ∫ x, mass (ψ.coreSlice s x) *
    potentialForm pairPotential (ψ.coreSlice s x).normalized) = _
  simp_rw [potentialForm_normalized_weight]
  exact integral_potentialForm_coreSlice ψ pairPotential ψ.core_pair_integrable

end Coulomb

end

end OAI
