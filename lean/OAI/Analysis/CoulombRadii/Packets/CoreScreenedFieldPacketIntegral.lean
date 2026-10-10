import Mathlib
import OAI.Analysis.CoulombRadii.Screening.CoreScreenedField
import OAI.Analysis.CoulombRadii.Localization.DensityCut

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
namespace Coulomb

lemma coreScreenedField_packet_integral {M m : ℕ} (S : Nuclei M) (u : H1Vector m)
    (g : 𝓢(Space,ℝ)) (ρ : Space → ℝ) (hp : ∀ x, 0 ≤ ρ x) (hm : Measurable ρ)
    (hi : Integrable ρ) :
    (∫ x, coreScreenedField S u x*packetDensity g ρ x) =
      (∫ x, attraction S x*packetDensity g ρ x) -
      (∫ x, coreCoulombPotential u x*packetDensity g ρ x) := by
  simp only [coreScreenedField,sub_mul]
  exact integral_sub (packetDensity_nuclear_integrable S g ρ hp hm hi)
    (coreCoulombPotential_mul_integrable u _ (packetDensity_integrable g ρ hp hm hi))

theorem packet_core_trial {M m : ℕ} (S : Nuclei M) (u : H1Vector m)
    (hu : Antisymmetric u) (hmu : mass u = 1)
    (g : 𝓢(Space,ℝ)) (hg : (∫ x : Space, g x^2) = 1)
    (hgc : HasCompactSupport (g : Space → ℝ))
    (ρ : Space → ℝ) (hp : ∀ y, 0 ≤ ρ y) (hm : Measurable ρ) (hi : Integrable ρ)
    (ht : Integrable (fun y => ρ y^(5/3:ℝ)))
    (K A : Set Space) (hK : IsCompact K) (hA : IsClosed A)
    (hs : ∀ y, y ∉ K → ρ y = 0) (hsu : SpatiallySupported u A)
    (hsep : Disjoint A (K+tsupport (g : Space → ℝ)))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, ∃ ψ : H1Vector n, Antisymmetric ψ ∧ mass ψ = 1 ∧
      form S ψ ≤ form S u +
        thomasFermiKineticConstant * (∫ y : Space, ρ y^(5/3:ℝ)) +
        (1/2:ℝ)*(∫ y : Space, ρ y)*(∑ b : Fin 3, ∫ x : Space,
          (fderiv ℝ g x (EuclideanSpace.single b 1))^2) -
        (∫ x, coreScreenedField S u x*packetDensity g ρ x) +
        (1/2:ℝ)*(∫ xy : Space × Space, coulombKernel (xy.1-xy.2)*
          (packetDensity g ρ xy.1*packetDensity g ρ xy.2)) + ε := by
  have hconv := packetDensity_cut_weighted_tendsto g ρ hp hm hi (attraction S)
    (attraction_nonneg S) (attraction_measurable S) (packetDensity_nuclear_integrable S g ρ hp hm hi)
  have hevent : ∀ᶠ k : ℕ in atTop,
      (∫ x, attraction S x*packetDensity g ρ x)-ε/2 <
        ∫ x, attraction S x*packetDensity g (densityCut ρ k) x :=
    hconv (eventually_gt_nhds (sub_lt_self _ (half_pos hε)))
  obtain ⟨k,hk⟩ := hevent.exists
  let σ := densityCut ρ k
  have hsp := densityCut_nonneg ρ hp k
  have hsm := densityCut_measurable ρ hm k
  have hsi := densityCut_integrable ρ hp hm hi k
  have hst := densityCut_kinetic_integrable ρ hp hm ht k
  obtain ⟨n,ψ,ha,hmu',he⟩ := bounded_packet_core_trial S u hu hmu g hg hgc σ hsp hsm hsi hst
    (k:ℝ) (densityCut_bound ρ k) K A hK hA (densityCut_support ρ K hs k) hsu hsep (ε/2) (half_pos hε)
  have hmass : (∫ y, σ y) ≤ ∫ y, ρ y := integral_mono hsi hi (densityCut_le ρ k)
  have hkt : (∫ y, σ y^(5/3:ℝ)) ≤ ∫ y, ρ y^(5/3:ℝ) :=
    integral_mono hst ht (fun y => Real.rpow_le_rpow (hsp y) (densityCut_le ρ k y) (by norm_num))
  have hcf : 0 ≤ thomasFermiKineticConstant := by unfold thomasFermiKineticConstant; positivity
  have hkin := mul_le_mul_of_nonneg_left hkt hcf
  have hgrad : 0 ≤ ∑ b : Fin 3, ∫ x : Space, (fderiv ℝ g x (EuclideanSpace.single b 1))^2 :=
    Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))
  have hmassgrad := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmass (by norm_num : (0:ℝ) ≤ 1/2)) hgrad
  have hdle := packetDensity_mono g σ ρ hsp hsm hsi hp hm hi (densityCut_le ρ k)
  have hcore := integral_mono
    (coreCoulombPotential_mul_integrable u _ (packetDensity_integrable g σ hsp hsm hsi))
    (coreCoulombPotential_mul_integrable u _ (packetDensity_integrable g ρ hp hm hi))
    (fun x => mul_le_mul_of_nonneg_left (hdle x) (coreCoulombPotential_nonneg u x))
  have hdirect := integral_mono (packetDensity_pair_integrable g σ hsp hsm hsi)
    (packetDensity_pair_integrable g ρ hp hm hi) (fun xy =>
      mul_le_mul_of_nonneg_left (mul_le_mul (hdle xy.1) (hdle xy.2)
        (packetDensity_nonneg g σ hsp _) (packetDensity_nonneg g ρ hp _)) (coulombKernel_nonneg _))
  rw [coreScreenedField_packet_integral S u g σ hsp hsm hsi] at he
  refine ⟨n,ψ,ha,hmu',?_⟩
  rw [coreScreenedField_packet_integral S u g ρ hp hm hi]
  change (∫ x, attraction S x*packetDensity g ρ x)-ε/2 < ∫ x, attraction S x*packetDensity g σ x at hk
  linarith
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise

end

end OAI
