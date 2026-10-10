import Mathlib
import OAI.Analysis.CoulombRadii.SpectralTheory.FermiPacketSpectralTrace
import OAI.Analysis.CoulombRadii.Packets.PacketIndex

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
namespace Coulomb
lemma hasSum_spin_duplicate {ι : Type*} {f : ι → ℝ} {a : ℝ}
    (hf : ∀ i, 0 ≤ f i) (hs : HasSum f a) :
    HasSum (fun i : ι × Fin 2 => f i.1) (2*a) := by
  have hsum : Summable (fun i : ι × Fin 2 => f i.1) := by
    apply (summable_prod_of_nonneg (fun i => hf i.1)).mpr
    refine ⟨fun _ => (hasSum_fintype _).summable, ?_⟩
    simpa only [tsum_fintype,Fin.sum_univ_two,← two_mul] using hs.summable.mul_left 2
  apply hsum.hasSum_iff.mpr
  rw [hsum.tsum_prod]
  simp only [tsum_fintype,Fin.sum_univ_two,← two_mul]
  rw [tsum_mul_left,hs.tsum_eq]

lemma packetBasis_eigen_nonneg (g : 𝓢(Space,ℂ)) (μ : Measure (Space × Space))
    [IsFiniteMeasure μ] (i : packetIndex g μ) : 0 ≤ i.1.re :=
  compactSpectralBasis_eigen_nonneg _ (packetFrame_compact g μ) (packetFrame_positive g μ) i

lemma packetBasis_eigen_le_one (g : 𝓢(Space,ℂ)) (hg : (∫ x : Space, ‖g x‖^2) = 1)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ] (hμ : μ ≤ volume.prod volume)
    (i : packetIndex g μ) : i.1.re ≤ 1 :=
  compactSpectralBasis_eigen_le_one _ (packetFrame_compact g μ) (packetFrame_positive g μ)
    (packetFrame_complement_positive g hg μ hμ) i

lemma packet_positive_hasSum {g : 𝓢(Space,ℂ)} {μ : Measure (Space × Space)}
    [IsFiniteMeasure μ] (f : packetIndex g μ → ℝ) {a : ℝ}
    (hs : HasSum (fun i => i.1.re*f i) a) :
    HasSum (fun i : positivePacketIndex g μ => i.val.1.re*f i.val) a := by
  apply (hasSum_subtype_iff_of_support_subset (s := {i : packetIndex g μ | 0 < i.1.re}) ?_).mpr hs
  intro i hi
  change 0 < i.1.re
  apply lt_of_le_of_ne (packetBasis_eigen_nonneg g μ i)
  intro he
  exact hi (by simp only [← he,zero_mul])

lemma packetPositive_density (g : 𝓢(Space,ℂ)) (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    (F : positivePacketIndex g μ → Space → ℂ)
    (he : ∀ i, (packetBasis g μ i.val : Space → ℂ) =ᵐ[volume] F i) :
    ∀ᵐ x ∂volume, HasSum
      (fun i : positivePacketIndex g μ × Fin 2 => i.1.val.1.re * ∑ s, ‖spinOrbital F i x s‖^2)
      (2*frameDensity (packetState_toL2_memLp g μ) x) := by
  let b := packetBasis g μ
  have hs : Summable (fun i : packetIndex g μ => i.1.re*‖b i‖^2) := by
    let : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
    have hnorm (i : packetIndex g μ) : ‖b i‖ = 1 := (packetBasis g μ).orthonormal.1 i
    simp only [hnorm,one_pow,mul_one]
    simpa only [packetIndex,packetFrame] using
      (frameOperator_spectral_hasSum (packetState_toL2_memLp g μ)).summable
  have h := l2_weighted_density_integrable b (fun i => i.1.re)
    (packetBasis_eigen_nonneg g μ) hs
  filter_upwards [h.2,ae_all_iff.mpr he] with x hx heq
  have hp := packet_positive_hasSum (g := g) (μ := μ) (fun i => ‖b i x‖^2) hx.hasSum
  have hp' : HasSum (fun i : positivePacketIndex g μ => i.val.1.re*‖F i x‖^2)
      (frameDensity (packetState_toL2_memLp g μ) x) := by
    convert hp using 1
    · ext i
      rw [heq i]
    · rfl
  simpa only [spinOrbital_density] using hasSum_spin_duplicate
    (fun i => mul_nonneg i.property.le (sq_nonneg _)) hp'

lemma packetPositive_directional_energy (g : 𝓢(Space,ℝ))
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    (hp : MemLp (fun yp : Space × Space => yp.2) 2 μ) (a : Space)
    (i : positivePacketIndex (complexWindow g) μ) (F : Space → ℂ)
    (hFs : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F)
    (he : (packetBasis (complexWindow g) μ i.val : Space → ℂ) =ᵐ[volume] F) :
    (∫ x : Space, ‖fderiv ℝ F x a‖^2) =
      ∫ ξ : Space, (2*Real.pi*inner ℝ ξ a)^2 *
        ‖(𝓕 (packetBasis (complexWindow g) μ i.val) : Lp ℂ 2 (volume : Measure Space)) ξ‖^2 := by
  obtain ⟨d,hd,heD⟩ := packetFrame_positive_eigen_weakDerivative g μ hp a i.val (ne_of_gt i.property)
  exact (weak_directional_smooth_norm_sq a F hFs hFc he hd).trans heD

lemma fermiPacket_positive_kinetic (g : 𝓢(Space,ℝ)) (hg : (∫ x : Space, g x^2) = 1)
    (ρ : Space → ℝ) (hρ : ∀ x, 0 ≤ ρ x) (hm : Measurable ρ) (hI : Integrable ρ)
    (hT : Integrable (fun x => ρ x^(5/3:ℝ))) :
    let μ := phaseMeasure (fermiRadius ρ)
    letI := fermiMeasure_finite ρ hρ hm hI
    ∀ (F : positivePacketIndex (complexWindow g) μ → Space → ℂ),
      (∀ i, ContDiff ℝ (⊤ : ℕ∞) (F i)) → (∀ i, HasCompactSupport (F i)) →
      (∀ i, (packetBasis (complexWindow g) μ i.val : Space → ℂ) =ᵐ[volume] F i) →
      HasSum (fun i : positivePacketIndex (complexWindow g) μ × Fin 2 =>
        i.1.val.1.re * ∑ s, ∑ b : Fin 3, ∫ x : Space,
          ‖fderiv ℝ (fun y => spinOrbital F i y s) x (EuclideanSpace.single b 1)‖^2)
        (2*(thomasFermiKineticConstant * (∫ y : Space, ρ y^(5/3:ℝ)) +
          (1/2:ℝ)*(∫ y : Space, ρ y)*∑ b : Fin 3, ∫ x : Space,
            (fderiv ℝ g x (EuclideanSpace.single b 1))^2)) := by
  dsimp only
  let := fermiMeasure_finite ρ hρ hm hI
  intro F hFs hFc he
  have hp := fermiMeasure_momentum_memLp ρ hρ hm hT
  have H := packet_positive_hasSum (g := complexWindow g) (μ := phaseMeasure (fermiRadius ρ))
    (fun i => ∑ b : Fin 3, ∫ ξ : Space, (2*Real.pi*inner ℝ ξ (EuclideanSpace.single b 1))^2 *
      ‖(𝓕 (packetBasis (complexWindow g) (phaseMeasure (fermiRadius ρ)) i) : Lp ℂ 2 (volume : Measure Space)) ξ‖^2)
    (fermiPacket_kinetic_trace g hg ρ hρ hm hI hT)
  have hedir (i : positivePacketIndex (complexWindow g) (phaseMeasure (fermiRadius ρ))) :
      (∑ b : Fin 3, ∫ x : Space, ‖fderiv ℝ (F i) x (EuclideanSpace.single b 1)‖^2) =
      ∑ b : Fin 3, ∫ ξ : Space, (2*Real.pi*inner ℝ ξ (EuclideanSpace.single b 1))^2 *
        ‖(𝓕 (packetBasis (complexWindow g) (phaseMeasure (fermiRadius ρ)) i.val) : Lp ℂ 2 (volume : Measure Space)) ξ‖^2 := by
    apply Finset.sum_congr rfl
    intro b _
    exact packetPositive_directional_energy g _ hp _ i (F i) (hFs i) (hFc i) (he i)
  simp_rw [← hedir] at H
  simpa only [spinOrbital_kinetic] using hasSum_spin_duplicate
    (fun i => mul_nonneg i.property.le (Finset.sum_nonneg (fun b _ => integral_nonneg (fun x => sq_nonneg _)))) H
end Coulomb

open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise

end

end OAI
