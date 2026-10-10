import Mathlib
import OAI.Analysis.CoulombRadii.FormDomain.OrbitalHilbertBasis
import OAI.Analysis.CoulombRadii.Packets.PacketSynthesisIndicator

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
abbrev packetIndex (g : 𝓢(Space,ℂ)) (μ : Measure (Space × Space)) :=
  Σ z, eigenspaceBasisSet (packetFrame g μ) z

def packetBasis (g : 𝓢(Space,ℂ)) (μ : Measure (Space × Space)) [IsFiniteMeasure μ] :
    HilbertBasis (packetIndex g μ) ℂ (Lp ℂ 2 (volume : Measure Space)) :=
  compactSpectralBasis (packetFrame g μ) (packetFrame_compact g μ)
    (frameOperator_symmetric (packetState_toL2_memLp g μ))

instance packetIndexCountable (g : 𝓢(Space,ℂ)) (μ : Measure (Space × Space)) [IsFiniteMeasure μ] :
    Countable (packetIndex g μ) := by
  let : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
  exact orthonormal_countable (packetBasis g μ).orthonormal

abbrev positivePacketIndex (g : 𝓢(Space,ℂ)) (μ : Measure (Space × Space)) :=
  {i : packetIndex g μ // 0 < i.1.re}

lemma positivePacketIndex_ne_zero {g : 𝓢(Space,ℂ)} {μ : Measure (Space × Space)}
    (i : positivePacketIndex g μ) : i.val.1 ≠ 0 := by
  intro h
  have hi := i.property
  rw [h] at hi
  exact lt_irrefl 0 hi

lemma packetPositiveIndex_smooth (g : 𝓢(Space,ℂ)) (hgc : HasCompactSupport (g : Space → ℂ))
    (A : Set (Space × Space)) (hA : MeasurableSet A)
    (K : Set Space) (hK : IsCompact K) (P : ℝ)
    (hAK : ∀ yp ∈ A, yp.1 ∈ K) (hAP : ∀ yp ∈ A, ‖yp.2‖ ≤ P) :
    letI := compactPhase_finite A K hK P hAK hAP
    ∃ F : positivePacketIndex g (volume.restrict A) → Space → ℂ,
      (∀ i, ContDiff ℝ (⊤ : ℕ∞) (F i)) ∧ (∀ i, HasCompactSupport (F i)) ∧
      (∀ i, (packetBasis g (volume.restrict A) i.val : Space → ℂ) =ᵐ[volume] F i) ∧
      (∀ i x, x ∉ K + tsupport (g : Space → ℂ) → F i x = 0) := by
  let := compactPhase_finite A K hK P hAK hAP
  have H (i : positivePacketIndex g (volume.restrict A)) :=
    packetFrame_eigen_smooth_supported g hgc A hA K hK P hAK hAP
      (packetBasis g (volume.restrict A) i.val) i.val.1 (positivePacketIndex_ne_zero i)
      (compactSpectralBasis_eigen _ _ _ i.val)
  choose F hs hc he hsup using H
  exact ⟨F,hs,hc,he,hsup⟩

lemma orthonormal_representative_inner {ι : Type*}
    (b : ι → Lp ℂ 2 (volume : Measure Space)) (hb : Orthonormal ℂ b)
    (F : ι → Space → ℂ) (he : ∀ i, (b i : Space → ℂ) =ᵐ[volume] F i) (i j : ι) :
    (∫ x : Space, star (F i x)*F j x) = if i = j then 1 else 0 := by
  classical
  have H : (∫ x : Space, star (F i x)*F j x) = inner ℂ (b i) (b j) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [he i,he j] with x hi hj
    simp only [RCLike.inner_apply',starRingEnd_apply,hi,hj]
  rw [H]
  exact orthonormal_iff_ite.mp hb i j

lemma spinOrbital_contDiff {ι : Type*} (F : ι → Space → ℂ)
    (hs : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (F i)) (i : ι × Fin 2) (s : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => spinOrbital F i x s) := by
  by_cases h : s = i.2 <;> simp only [spinOrbital,h,ite_true,ite_false]
  · exact hs i.1
  · exact contDiff_const

lemma spinOrbital_compactSupport {ι : Type*} (F : ι → Space → ℂ)
    (hc : ∀ i, HasCompactSupport (F i)) (i : ι × Fin 2) (s : Fin 2) :
    HasCompactSupport (fun x => spinOrbital F i x s) := by
  by_cases h : s = i.2 <;> simp only [spinOrbital,h,ite_true,ite_false]
  · exact hc i.1
  · exact HasCompactSupport.zero

lemma spinOrbital_support {ι : Type*} (F : ι → Space → ℂ) (B : Set Space)
    (hB : ∀ i x, x ∉ B → F i x = 0) (i : ι × Fin 2) (s : Fin 2) (x : Space) (hx : x ∉ B) :
    spinOrbital F i x s = 0 := by simp only [spinOrbital,hB i.1 x hx,ite_self]

lemma spinOrbital_density {ι : Type*} (F : ι → Space → ℂ) (i : ι × Fin 2) (x : Space) :
    (∑ s : Fin 2, ‖spinOrbital F i x s‖^2) = ‖F i.1 x‖^2 := by
  simp only [spinOrbital,apply_ite,norm_zero,ite_pow,zero_pow (by decide : 2 ≠ 0)]
  simp

lemma spinOrbital_kinetic {ι : Type*} (F : ι → Space → ℂ) (i : ι × Fin 2) :
    (∑ s : Fin 2, ∑ b : Fin 3, ∫ x : Space,
      ‖fderiv ℝ (fun y => spinOrbital F i y s) x (EuclideanSpace.single b 1)‖^2) =
    ∑ b : Fin 3, ∫ x : Space, ‖fderiv ℝ (F i.1) x (EuclideanSpace.single b 1)‖^2 := by
  have he (s : Fin 2) : (∑ b : Fin 3, ∫ x : Space,
      ‖fderiv ℝ (fun y => spinOrbital F i y s) x (EuclideanSpace.single b 1)‖^2) =
      if s = i.2 then ∑ b : Fin 3, ∫ x : Space,
        ‖fderiv ℝ (F i.1) x (EuclideanSpace.single b 1)‖^2 else 0 := by
    by_cases h : s = i.2 <;> simp [spinOrbital,h]
  simp only [he]
  simp
end Coulomb

end

end OAI
