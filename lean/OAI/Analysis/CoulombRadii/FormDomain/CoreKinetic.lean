import Mathlib
import OAI.Analysis.CoulombRadii.Propagation.NuclearPotentialSplitJoin

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

lemma potentialForm_coreSlice_parameter_ae {m k : ℕ} (ψ : H1Vector (m+k)) (s : Spins m)
    (V : Configuration m → Configuration k → ℝ) :
    (fun x => potentialForm (V x) (ψ.coreSlice s x)) =ᵐ[volume]
      fun x => ∑ t : Spins k, ∫ y, V x y * ‖ψ.value (Fin.append s t) (joinConfiguration m k (x,y))‖^2 := by
  filter_upwards [ψ.coreSliceRegular_ae s] with x hx
  simp only [potentialForm, ψ.coreSlice_value s hx]

lemma potentialForm_coreSlice_parameter_integrable {m k : ℕ} (ψ : H1Vector (m+k))
    (s : Spins m) (V : Configuration m → Configuration k → ℝ)
    (hV : ∀ t : Spins k, Integrable (fun z =>
      V ((joinConfiguration m k).symm z).1 ((joinConfiguration m k).symm z).2 *
        ‖ψ.value (Fin.append s t) z‖^2)) :
    Integrable (fun x => potentialForm (V x) (ψ.coreSlice s x)) := by
  apply Integrable.congr _ (potentialForm_coreSlice_parameter_ae ψ s V).symm
  apply integrable_finsetSum
  intro t _
  have H := ((joinConfiguration_measurePreserving m k).integrable_comp_emb
    (joinConfiguration m k).toHomeomorph.toMeasurableEquiv.measurableEmbedding).mpr (hV t)
  change Integrable (fun z : Configuration m × Configuration k =>
    V ((joinConfiguration m k).symm (joinConfiguration m k z)).1
      ((joinConfiguration m k).symm (joinConfiguration m k z)).2 *
        ‖ψ.value (Fin.append s t) (joinConfiguration m k z)‖^2) (volume.prod volume) at H
  simp only [ContinuousLinearEquiv.symm_apply_apply] at H
  exact H.integral_prod_left

lemma integral_potentialForm_coreSlice_parameter {m k : ℕ} (ψ : H1Vector (m+k))
    (V : Configuration m → Configuration k → ℝ)
    (hV : ∀ st : Spins (m+k), Integrable (fun z =>
      V ((joinConfiguration m k).symm z).1 ((joinConfiguration m k).symm z).2 * ‖ψ.value st z‖^2)) :
    (∑ s : Spins m, ∫ x, potentialForm (V x) (ψ.coreSlice s x)) =
      ∑ st : Spins (m+k), ∫ z,
        V ((joinConfiguration m k).symm z).1 ((joinConfiguration m k).symm z).2 * ‖ψ.value st z‖^2 := by
  have hs (s : Spins m) : (∫ x, potentialForm (V x) (ψ.coreSlice s x)) =
      ∑ t : Spins k, ∫ z,
        V ((joinConfiguration m k).symm z).1 ((joinConfiguration m k).symm z).2 *
          ‖ψ.value (Fin.append s t) z‖^2 := by
    rw [integral_congr_ae (potentialForm_coreSlice_parameter_ae ψ s V)]
    have hi (t : Spins k) : Integrable (fun z : Configuration m × Configuration k =>
        V z.1 z.2 * ‖ψ.value (Fin.append s t) (joinConfiguration m k z)‖^2) (volume.prod volume) := by
      have H := ((joinConfiguration_measurePreserving m k).integrable_comp_emb
        (joinConfiguration m k).toHomeomorph.toMeasurableEquiv.measurableEmbedding).mpr
        (hV (Fin.append s t))
      change Integrable (fun z : Configuration m × Configuration k =>
        V ((joinConfiguration m k).symm (joinConfiguration m k z)).1
          ((joinConfiguration m k).symm (joinConfiguration m k z)).2 *
          ‖ψ.value (Fin.append s t) (joinConfiguration m k z)‖^2) (volume.prod volume) at H
      simpa only [ContinuousLinearEquiv.symm_apply_apply] using H
    rw [integral_finsetSum _ (fun t _ => (hi t).integral_prod_left)]
    apply Finset.sum_congr rfl
    intro t _
    rw [← integral_prod _ (hi t)]
    have H := (joinConfiguration_measurePreserving m k).integral_comp'
      (fun z => V ((joinConfiguration m k).symm z).1 ((joinConfiguration m k).symm z).2 *
        ‖ψ.value (Fin.append s t) z‖^2)
    change (∫ z : Configuration m × Configuration k,
        V ((joinConfiguration m k).symm (joinConfiguration m k z)).1
          ((joinConfiguration m k).symm (joinConfiguration m k z)).2 *
          ‖ψ.value (Fin.append s t) (joinConfiguration m k z)‖^2 ∂volume.prod volume) = _ at H
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using H
  simp_rw [hs]
  rw [← Fintype.sum_prod_type (f := fun st : Spins m × Spins k =>
    ∫ z, V ((joinConfiguration m k).symm z).1 ((joinConfiguration m k).symm z).2 *
      ‖ψ.value (Fin.append st.1 st.2) z‖^2)]
  exact Fintype.sum_equiv (Fin.appendEquiv m k) _ _ (fun _ => rfl)

lemma potentialForm_const {n : ℕ} (c : ℝ) (ψ : H1Vector n) :
    potentialForm (fun _ => c) ψ = c * mass ψ := by
  simp only [potentialForm, mass, integral_const_mul, Finset.mul_sum]

lemma H1Vector.outer_nuclear_integrable {M m k : ℕ} (ψ : H1Vector (m+k))
    (S : Nuclei M) (st : Spins (m+k)) :
    Integrable (fun z => nuclearPotential S ((joinConfiguration m k).symm z).1 * ‖ψ.value st z‖^2) := by
  simp only [nuclearPotential, attraction, position_split_left, Finset.sum_mul]
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  have H := (ψ.nuclear_coulomb_integrable_bound st (Fin.castAdd k i) (S.position j)
    (by norm_num : (0:ℝ)<1)).1
  simpa only [mul_assoc] using H.const_mul (S.charge j)

lemma H1Vector.outer_pair_integrable {m k : ℕ} (ψ : H1Vector (m+k)) (st : Spins (m+k)) :
    Integrable (fun z => pairPotential ((joinConfiguration m k).symm z).1 * ‖ψ.value st z‖^2) := by
  simp only [pairPotential, position_split_left, Finset.sum_mul]
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  by_cases hij : i < j
  · simp only [ite_eq_left hij]
    exact (ψ.pair_coulomb_integrable_bound st (Fin.castAdd k i) (Fin.castAdd k j)
      (fun he => hij.ne (by apply Fin.ext; have H := congrArg Fin.val he; simpa only [Fin.val_castAdd] using H)) (by norm_num : (0:ℝ)<1)).1
  · simp only [ite_eq_right hij, zero_mul]
    exact integrable_zero _ _ _

lemma H1Vector.cross_integrable {m k : ℕ} (ψ : H1Vector (m+k)) (st : Spins (m+k)) :
    Integrable (fun z => crossPotential ((joinConfiguration m k).symm z).1
      ((joinConfiguration m k).symm z).2 * ‖ψ.value st z‖^2) := by
  simp only [crossPotential, position_split_left, position_split_right, Finset.sum_mul]
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  exact (ψ.pair_coulomb_integrable_bound st (Fin.castAdd k i) (Fin.natAdd m j)
    (by intro h; have H := congrArg Fin.val h
        simp only [Fin.val_castAdd, Fin.val_natAdd] at H; omega)
    (by norm_num : (0:ℝ)<1)).1

noncomputable def coreKinetic {m k : ℕ} (ψ : H1Vector (m+k)) : ℝ :=
  (1/2 : ℝ) * ∑ st : Spins (m+k), ∑ a : Fin k × Fin 3,
    ∫ z, ‖ψ.gradient st (Fin.natAdd m a.1,a.2) z‖^2
noncomputable def outerKinetic {m k : ℕ} (ψ : H1Vector (m+k)) : ℝ :=
  (1/2 : ℝ) * ∑ st : Spins (m+k), ∑ a : Fin m × Fin 3,
    ∫ z, ‖ψ.gradient st (Fin.castAdd k a.1,a.2) z‖^2

lemma kinetic_split {m k : ℕ} (ψ : H1Vector (m+k)) :
    kinetic ψ = coreKinetic ψ + outerKinetic ψ := by
  simp only [kinetic, coreKinetic, outerKinetic, Fintype.sum_prod_type, Fin.sum_univ_add,
    Finset.sum_add_distrib, mul_add]
  ring

lemma nuclearEnergy_split {M m k : ℕ} (S : Nuclei M) (ψ : H1Vector (m+k)) :
    nuclearEnergy S ψ =
      potentialForm (fun z => nuclearPotential S ((joinConfiguration m k).symm z).1) ψ +
      potentialForm (fun z => nuclearPotential S ((joinConfiguration m k).symm z).2) ψ := by
  have hp (z : Configuration (m+k)) : nuclearPotential S z =
      nuclearPotential S ((joinConfiguration m k).symm z).1 +
        nuclearPotential S ((joinConfiguration m k).symm z).2 := by
    simpa only [Prod.mk.eta, ContinuousLinearEquiv.apply_symm_apply] using
      nuclearPotential_split_join S ((joinConfiguration m k).symm z).1 ((joinConfiguration m k).symm z).2
  change potentialForm (nuclearPotential S) ψ = _
  simp only [potentialForm, hp, add_mul]
  simp_rw [integral_add (ψ.outer_nuclear_integrable S _) (ψ.core_nuclear_integrable S _)]
  exact Finset.sum_add_distrib

lemma pairEnergy_split {m k : ℕ} (ψ : H1Vector (m+k)) :
    pairEnergy ψ =
      potentialForm (fun z => pairPotential ((joinConfiguration m k).symm z).1) ψ +
      potentialForm (fun z => pairPotential ((joinConfiguration m k).symm z).2) ψ +
      potentialForm (fun z => crossPotential ((joinConfiguration m k).symm z).1
        ((joinConfiguration m k).symm z).2) ψ := by
  have hp (z : Configuration (m+k)) : pairPotential z =
      pairPotential ((joinConfiguration m k).symm z).1 +
        pairPotential ((joinConfiguration m k).symm z).2 +
        crossPotential ((joinConfiguration m k).symm z).1 ((joinConfiguration m k).symm z).2 := by
    simpa only [Prod.mk.eta, ContinuousLinearEquiv.apply_symm_apply, crossPotential] using
      pairPotential_split_join ((joinConfiguration m k).symm z).1 ((joinConfiguration m k).symm z).2
  change potentialForm pairPotential ψ = _
  simp only [potentialForm, hp, add_mul]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro st _
  have H := integral_add ((ψ.outer_pair_integrable st).add (ψ.core_pair_integrable st))
    (ψ.cross_integrable st)
  simp only [Pi.add_apply] at H
  rw [H, integral_add (ψ.outer_pair_integrable st) (ψ.core_pair_integrable st)]

lemma form_normalized_weight {M n : ℕ} (S : Nuclei M) (ψ : H1Vector n) :
    mass ψ * form S ψ.normalized = form S ψ := by
  change mass ψ * (kinetic ψ.normalized - potentialForm (nuclearPotential S) ψ.normalized +
    potentialForm pairPotential ψ.normalized) = _
  rw [mul_add, mul_sub, kinetic_normalized_weight, potentialForm_normalized_weight,
    potentialForm_normalized_weight]
  rfl

lemma form_coreSlice_integrable {M m k : ℕ} (S : Nuclei M) (ψ : H1Vector (m+k)) (s : Spins m) :
    Integrable (fun x => form S (ψ.coreSlice s x)) :=
  ((kinetic_coreSlice_integrable ψ s).sub
    (potentialForm_coreSlice_integrable ψ s (nuclearPotential S)
      (fun t => ψ.core_nuclear_integrable S (Fin.append s t)))).add
        (potentialForm_coreSlice_integrable ψ s pairPotential
          (fun t => ψ.core_pair_integrable (Fin.append s t)))

lemma conditional_core_form_identity {M m k : ℕ} (S : Nuclei M) (ψ : H1Vector (m+k)) :
    (∑ s : Spins m, ∫ x, mass (ψ.coreSlice s x) * form S (ψ.coreSlice s x).normalized) =
      coreKinetic ψ - potentialForm (fun z => nuclearPotential S ((joinConfiguration m k).symm z).2) ψ +
        potentialForm (fun z => pairPotential ((joinConfiguration m k).symm z).2) ψ := by
  simp_rw [form_normalized_weight]
  change (∑ s : Spins m, ∫ x, kinetic (ψ.coreSlice s x) -
    potentialForm (nuclearPotential S) (ψ.coreSlice s x) + potentialForm pairPotential (ψ.coreSlice s x)) = _
  have he (s : Spins m) :
      (∫ x, kinetic (ψ.coreSlice s x) - potentialForm (nuclearPotential S) (ψ.coreSlice s x) +
        potentialForm pairPotential (ψ.coreSlice s x)) =
      (∫ x, kinetic (ψ.coreSlice s x)) - (∫ x, potentialForm (nuclearPotential S) (ψ.coreSlice s x)) +
        ∫ x, potentialForm pairPotential (ψ.coreSlice s x) := by
    have H := integral_add ((kinetic_coreSlice_integrable ψ s).sub
      (potentialForm_coreSlice_integrable ψ s (nuclearPotential S)
        (fun t => ψ.core_nuclear_integrable S (Fin.append s t))))
      (potentialForm_coreSlice_integrable ψ s pairPotential
        (fun t => ψ.core_pair_integrable (Fin.append s t)))
    simp only [Pi.sub_apply] at H
    rw [H, integral_sub (kinetic_coreSlice_integrable ψ s)
        (potentialForm_coreSlice_integrable ψ s (nuclearPotential S)
          (fun t => ψ.core_nuclear_integrable S (Fin.append s t)))]
  simp only [he, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [integral_kinetic_coreSlice, integral_potentialForm_coreSlice ψ (nuclearPotential S)
    (ψ.core_nuclear_integrable S), integral_potentialForm_coreSlice ψ pairPotential ψ.core_pair_integrable]
  rfl

end Coulomb

end

end OAI
