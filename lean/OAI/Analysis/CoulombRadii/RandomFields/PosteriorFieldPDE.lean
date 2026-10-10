import Mathlib
import OAI.Analysis.CoulombRadii.RandomFields.PhysicalPosteriorInverse

namespace OAI

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace NeutralAtom

lemma atomic_screenedField_weakLaplacian {ρ : Position → ℝ} (hi : Integrable ρ)
    (hc : Continuous (potentialOf ρ)) (Z : ℝ) {U : Set Position} (hU : (0:Position) ∉ U) :
    HasWeakLaplacian (fun x => Z*coulombKernel x-potentialOf ρ x) U
      (fun x => 4*Real.pi*ρ x) := by
  intro φ hφ hφc ht
  have hL := continuous_coordinateLaplacian (hφ.of_le (by exact WithTop.coe_le_coe.mpr le_top))
  have hLc := hasCompactSupport_coordinateLaplacian hφc
  have hts : tsupport (coordinateLaplacian φ) ⊆ tsupport φ := by
    apply closure_minimal _ (isClosed_tsupport _)
    intro x hx
    by_contra hn
    exact hx (coordinateLaplacian_eq_zero_of_notMem_tsupport hn)
  have hK : Integrable (fun x => coulombKernel x*coordinateLaplacian φ x) := by
    apply integrable_mul_compact_of_continuousAt _ hL hLc
    intro x hx
    have hn : x≠0 := fun he => hU (he ▸ ht (hts hx))
    exact continuous_norm.continuousAt.inv₀ (norm_ne_zero_iff.mpr hn)
  have hP : Integrable (fun x => potentialOf ρ x*coordinateLaplacian φ x) :=
    (hc.mul hL).integrable_of_hasCompactSupport hLc.mul_left
  have he : (∫ x,coulombKernel x*coordinateLaplacian φ x)=0 := by
    rw [integral_coulombKernel_laplacian hφ hφc,
      image_eq_zero_of_notMem_tsupport (fun h => hU (ht h))]
    ring
  simp_rw [sub_mul,mul_assoc]
  rw [integral_sub (hK.const_mul Z) hP,integral_const_mul,he,mul_zero,
    potentialOf_weakLaplacian hi φ hφ hφc (fun _ _ => mem_univ _)]
  simp only [neg_mul,integral_neg,zero_sub,neg_neg]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

lemma conditionalPacketField_weakLaplacian {Ω B : Type*}
    [MeasurableSpace Ω] [MeasurableSpace B] {n : ℕ}
    (P : Measure Ω) [IsFiniteMeasure P] (raw : Ω → Configuration n) (obs : Ω → B)
    {g : Position → ℝ} (hg : Continuous g) (hgs : HasCompactSupport g)
    (hm : (∫ z,g z^2)=1) {c r₀ s : ℝ}
    (hc : 0<c) (hr : 0<r₀) (hs : 0<s) (datum : B)
    (Z : ℝ) {U : Set Position} (hU : (0:Position) ∉ U) :
    HasWeakLaplacian (fun x => Z*coulombKernel x-potentialOf
      (conditionalPacketDensity P raw obs g c r₀ s datum) x) U
      (fun x => 4*Real.pi*conditionalPacketDensity P raw obs g c r₀ s datum x) :=
  atomic_screenedField_weakLaplacian (mixturePacketDensity_integrable hg hm hc hr hs _)
    (conditionalPacketPotential_continuous P raw obs hg hgs hm hc hr hs datum) Z hU

lemma conditionalPacketField_continuousOn {Ω B : Type*}
    [MeasurableSpace Ω] [MeasurableSpace B] {n : ℕ}
    (P : Measure Ω) [IsFiniteMeasure P] (raw : Ω → Configuration n) (obs : Ω → B)
    {g : Position → ℝ} (hg : Continuous g) (hgs : HasCompactSupport g)
    (hm : (∫ z,g z^2)=1) {c r₀ s : ℝ}
    (hc : 0<c) (hr : 0<r₀) (hs : 0<s) (datum : B)
    (Z : ℝ) {U : Set Position} (hU : (0:Position) ∉ U) :
    ContinuousOn (fun x => Z*coulombKernel x-potentialOf
      (conditionalPacketDensity P raw obs g c r₀ s datum) x) U := by
  apply ContinuousOn.sub _
    (conditionalPacketPotential_continuous P raw obs hg hgs hm hc hr hs datum).continuousOn
  apply ContinuousOn.mul continuousOn_const
  exact continuous_norm.continuousOn.inv₀ (fun x hx => norm_ne_zero_iff.mpr
    (fun he => hU (he ▸ hx)))
end NeutralAtom
end

end

end OAI
