import Mathlib
import OAI.Analysis.CoulombRadii.FormDomain.CoreKinetic

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

noncomputable def conditionalEnergy {M m k : ℕ} (S : Nuclei M) (ψ : H1Vector (m+k))
    (s : Spins m) (x : Configuration m) : ℝ :=
  form S (ψ.coreSlice s x).normalized - nuclearPotential S x + pairPotential x +
    potentialForm (crossPotential x) (ψ.coreSlice s x).normalized

lemma conditionalEnergy_weight {M m k : ℕ} (S : Nuclei M) (ψ : H1Vector (m+k))
    (s : Spins m) (x : Configuration m) :
    mass (ψ.coreSlice s x) * conditionalEnergy S ψ s x =
      form S (ψ.coreSlice s x) -
        potentialForm (fun _ : Configuration k => nuclearPotential S x) (ψ.coreSlice s x) +
        potentialForm (fun _ : Configuration k => pairPotential x) (ψ.coreSlice s x) +
        potentialForm (crossPotential x) (ψ.coreSlice s x) := by
  simp only [conditionalEnergy, mul_add, mul_sub, form_normalized_weight,
    potentialForm_normalized_weight, potentialForm_const]
  ring

lemma conditionalEnergy_weight_integrable {M m k : ℕ} (S : Nuclei M)
    (ψ : H1Vector (m+k)) (s : Spins m) :
    Integrable (fun x => mass (ψ.coreSlice s x) * conditionalEnergy S ψ s x) := by
  simp only [conditionalEnergy_weight]
  exact (((form_coreSlice_integrable S ψ s).sub
    (potentialForm_coreSlice_parameter_integrable ψ s (fun x _ => nuclearPotential S x)
      (fun t => ψ.outer_nuclear_integrable S (Fin.append s t)))).add
    (potentialForm_coreSlice_parameter_integrable ψ s (fun x _ => pairPotential x)
      (fun t => ψ.outer_pair_integrable (Fin.append s t)))).add
    (potentialForm_coreSlice_parameter_integrable ψ s crossPotential
      (fun t => ψ.cross_integrable (Fin.append s t)))

lemma conditional_energy_identity {M m k : ℕ} (S : Nuclei M) (ψ : H1Vector (m+k)) :
    form S ψ = outerKinetic ψ +
      ∑ s : Spins m, ∫ x, mass (ψ.coreSlice s x) * conditionalEnergy S ψ s x := by
  have hi (s : Spins m) :
      (∫ x, mass (ψ.coreSlice s x) * conditionalEnergy S ψ s x) =
      (∫ x, form S (ψ.coreSlice s x)) -
      (∫ x, potentialForm (fun _ : Configuration k => nuclearPotential S x) (ψ.coreSlice s x)) +
      (∫ x, potentialForm (fun _ : Configuration k => pairPotential x) (ψ.coreSlice s x)) +
      (∫ x, potentialForm (crossPotential x) (ψ.coreSlice s x)) := by
    simp only [conditionalEnergy_weight]
    have hn := potentialForm_coreSlice_parameter_integrable ψ s (fun x _ => nuclearPotential S x)
      (fun t => ψ.outer_nuclear_integrable S (Fin.append s t))
    have hp := potentialForm_coreSlice_parameter_integrable ψ s (fun x _ => pairPotential x)
      (fun t => ψ.outer_pair_integrable (Fin.append s t))
    have hc := potentialForm_coreSlice_parameter_integrable ψ s crossPotential
      (fun t => ψ.cross_integrable (Fin.append s t))
    have hf := form_coreSlice_integrable S ψ s
    have H := integral_add ((hf.sub hn).add hp) hc
    simp only [Pi.sub_apply, Pi.add_apply] at H
    rw [H]
    have H' := integral_add (hf.sub hn) hp
    simp only [Pi.sub_apply] at H'
    rw [H', integral_sub hf hn]
  simp only [hi, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [integral_potentialForm_coreSlice_parameter ψ (fun x _ => nuclearPotential S x)
      (ψ.outer_nuclear_integrable S),
    integral_potentialForm_coreSlice_parameter ψ (fun x _ => pairPotential x) ψ.outer_pair_integrable,
    integral_potentialForm_coreSlice_parameter ψ crossPotential ψ.cross_integrable]
  have hc := conditional_core_form_identity S ψ
  simp only [form_normalized_weight] at hc
  rw [hc]
  change kinetic ψ - nuclearEnergy S ψ + pairEnergy ψ = _
  rw [kinetic_split, nuclearEnergy_split, pairEnergy_split]
  simp only [potentialForm]
  ring

lemma outerKinetic_nonneg {m k : ℕ} (ψ : H1Vector (m+k)) : 0 ≤ outerKinetic ψ := by
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _)

end Coulomb

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical

end

end OAI
