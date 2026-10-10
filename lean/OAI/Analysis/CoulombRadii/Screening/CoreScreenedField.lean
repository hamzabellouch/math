import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.SumSpinDuplicate
import OAI.Analysis.CoulombRadii.Packets.PacketDensity

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
namespace Coulomb

lemma boundedDensity_nuclear_integrable {M : ℕ} (S : Nuclei M) (d : Space → ℝ)
    (hd : Integrable d) (hm : Measurable d) (hp : ∀ x, 0 ≤ d x)
    (C : ℝ) (hC : ∀ x, d x ≤ C) : Integrable (fun x => attraction S x*d x) := by
  simp only [attraction,Finset.sum_mul]
  apply integrable_finsetSum
  intro j _
  have H := (coulomb_convolution_integrable hd hm hp hC (by norm_num : (0:ℝ)<1) (S.position j)).const_mul (S.charge j)
  apply H.congr
  filter_upwards [] with x
  rw [coulombKernel_sub_comm (S.position j)]
  ring

lemma packetDensity_nuclear_integrable {M : ℕ} (S : Nuclei M)
    (g : 𝓢(Space,ℝ)) (ρ : Space → ℝ) (hp : ∀ y, 0 ≤ ρ y)
    (hm : Measurable ρ) (hi : Integrable ρ) :
    Integrable (fun x => attraction S x*packetDensity g ρ x) :=
  boundedDensity_nuclear_integrable S _ (packetDensity_integrable g ρ hp hm hi)
    (packetDensity_measurable g ρ hm) (packetDensity_nonneg g ρ hp) _
    (packetDensity_bound g ρ hp hm hi)

lemma packetDensity_pair_integrable (g : 𝓢(Space,ℝ)) (ρ : Space → ℝ)
    (hp : ∀ y, 0 ≤ ρ y) (hm : Measurable ρ) (hi : Integrable ρ) :
    Integrable (fun xy : Space × Space => coulombKernel (xy.1-xy.2)*
      (packetDensity g ρ xy.1*packetDensity g ρ xy.2)) := by
  have hd := packetDensity_integrable g ρ hp hm hi
  have hdm := packetDensity_measurable g ρ hm
  have H := coulomb_pair_integrable hd hdm hd hdm (fun y => by
    rw [Real.norm_of_nonneg (packetDensity_nonneg g ρ hp y)]
    exact packetDensity_bound g ρ hp hm hi y)
  apply H.congr
  filter_upwards [] with xy
  ring

lemma packetPositive_orthonormal (g : 𝓢(Space,ℂ)) (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    (F : positivePacketIndex g μ → Space → ℂ)
    (he : ∀ i, (packetBasis g μ i.val : Space → ℂ) =ᵐ[volume] F i) :
    ∀ i j, (∫ x : Space, star (F i x)*F j x) = @ite ℂ (i = j) (Classical.propDecidable _) 1 0 := by
  have ho : Orthonormal ℂ (fun i : positivePacketIndex g μ => packetBasis g μ i.val) :=
    (packetBasis g μ).orthonormal.comp (fun i : positivePacketIndex g μ => i.val) Subtype.val_injective
  exact orthonormal_representative_inner (fun i : positivePacketIndex g μ => packetBasis g μ i.val) ho F he

def coreScreenedField {M m : ℕ} (S : Nuclei M) (u : H1Vector m) (x : Space) : ℝ :=
  attraction S x - coreCoulombPotential u x

theorem bounded_packet_core_trial {M m : ℕ} (S : Nuclei M) (u : H1Vector m)
    (hu : Antisymmetric u) (hmu : mass u = 1)
    (g : 𝓢(Space,ℝ)) (hg : (∫ x : Space, g x^2) = 1)
    (hgc : HasCompactSupport (g : Space → ℝ))
    (ρ : Space → ℝ) (hp : ∀ y, 0 ≤ ρ y) (hm : Measurable ρ) (hi : Integrable ρ)
    (ht : Integrable (fun y => ρ y^(5/3:ℝ))) (C : ℝ) (hC : ∀ y, ρ y ≤ C)
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
  let μ := volume.restrict (phaseRegion (fermiRadius ρ))
  let : IsFiniteMeasure (volume.restrict (phaseRegion (fermiRadius ρ))) := fermiMeasure_finite ρ hp hm hi
  let : Countable (packetIndex (complexWindow g) (volume.restrict (phaseRegion (fermiRadius ρ)))) := packetIndexCountable _ _
  let : Countable (positivePacketIndex (complexWindow g) (volume.restrict (phaseRegion (fermiRadius ρ)))) := inferInstance
  obtain ⟨F,hFs,hFc,he,hSup⟩ := packetPositiveIndex_smooth (complexWindow g)
    (complexWindow_compactSupport g hgc) (phaseRegion (fermiRadius ρ))
    (phaseRegion_measurable (fermiRadius_measurable ρ hm)) K hK
    ((3/(8*Real.pi)*C)^(1/3:ℝ)) (fermiPhase_center_mem ρ K hs)
    (fermiPhase_momentum_bound ρ hp C hC)
  have hsup : ∀ i x, x ∉ K+tsupport (g : Space → ℝ) → F i x = 0 := by
    simpa only [complexWindow_tsupport] using hSup
  have ho : ∀ i j, (∫ x : Space, star (F i x)*F j x) = @ite ℂ (i = j) (Classical.propDecidable _) 1 0 := by
    exact packetPositive_orthonormal (complexWindow g) μ F he
  have hg' : (∫ x : Space, ‖complexWindow g x‖^2) = 1 := by
    simpa only [complexWindow_apply,Complex.norm_real,Real.norm_eq_abs,sq_abs] using hg
  have hdens := packetPositive_density (complexWindow g) μ F he
  have hde : (fun x => ∑' i : positivePacketIndex (complexWindow g) μ × Fin 2,
      i.1.val.1.re*∑ s, ‖spinOrbital F i x s‖^2) =ᵐ[volume] packetDensity g ρ := by
    filter_upwards [hdens,fermiPacket_density g ρ hp hm hi] with x hx hy
    exact hx.tsum_eq.trans hy
  have hkin := fermiPacket_positive_kinetic g hg ρ hp hm hi ht F hFs hFc he
  have hnuc := packetDensity_nuclear_integrable S g ρ hp hm hi
  have hcor := coreCoulombPotential_mul_integrable u _ (packetDensity_integrable g ρ hp hm hi)
  have hfield : (∫ x, coreScreenedField S u x*packetDensity g ρ x) =
      (∫ x, attraction S x*packetDensity g ρ x) -
      (∫ x, coreCoulombPotential u x*packetDensity g ρ x) := by
    simp only [coreScreenedField,sub_mul]
    exact integral_sub hnuc hcor
  obtain ⟨n,ψ,hψa,hψm,hψe⟩ := infinite_fermi_core_trial S u hu hmu A
    (K+tsupport (g : Space → ℝ)) hA (hK.add hgc).isClosed hsep hsu
    (spinOrbital F) (spinOrbital_contDiff F hFs) (spinOrbital_compactSupport F hFc)
    (spinOrbital_support F _ hsup) (fun i j => by
      by_cases hij : i = j
      · simpa only [ite_eq_left hij] using spinOrbital_orthonormal F ho i j
      · simpa only [ite_eq_right hij] using spinOrbital_orthonormal F ho i j)
    (fun i => i.1.val.1.re) (fun i => i.1.property.le)
    (fun i => packetBasis_eigen_le_one (complexWindow g) hg' μ (phaseMeasure_le _) i.1.val)
    (packetDensity g ρ) (packetDensity_integrable g ρ hp hm hi)
    (hdens.mono (fun _ hx => hx.summable)) hde hnuc
    (packetDensity_pair_integrable g ρ hp hm hi) hkin.summable ε hε
  refine ⟨n,ψ,hψa,hψm,?_⟩
  dsimp only [phaseMeasure] at hkin
  change HasSum (fun i : positivePacketIndex (complexWindow g) (volume.restrict (phaseRegion (fermiRadius ρ))) × Fin 2 =>
    i.1.val.1.re*∑ s, ∑ b : Fin 3, ∫ x : Space,
      ‖fderiv ℝ (fun y => spinOrbital F i y s) x (EuclideanSpace.single b 1)‖^2) _ at hkin
  rw [hkin.tsum_eq] at hψe
  rw [hfield]
  linarith
end Coulomb

open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise

end

end OAI
