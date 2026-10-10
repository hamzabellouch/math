import Mathlib
import OAI.Analysis.CoulombRadii.SpectralTheory.FermiPacketSpectralTrace

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
namespace Coulomb

def packetDensity (g : 𝓢(Space,ℝ)) (ρ : Space → ℝ) (x : Space) : ℝ :=
  ∫ y : Space, g (x-y)^2*ρ y

lemma packetDensity_nonneg (g : 𝓢(Space,ℝ)) (ρ : Space → ℝ) (hp : ∀ y, 0 ≤ ρ y) (x : Space) :
    0 ≤ packetDensity g ρ x := integral_nonneg (fun y => mul_nonneg (sq_nonneg _) (hp y))

lemma packetDensity_measurable (g : 𝓢(Space,ℝ)) (ρ : Space → ℝ) (hm : Measurable ρ) :
    Measurable (packetDensity g ρ) := by
  exact (((g.continuous.measurable.comp (measurable_fst.sub measurable_snd)).pow_const 2).mul
    (hm.comp measurable_snd)).stronglyMeasurable.integral_prod_right.measurable

lemma packetDensity_integrable (g : 𝓢(Space,ℝ)) (ρ : Space → ℝ) (hp : ∀ y, 0 ≤ ρ y)
    (hm : Measurable ρ) (hi : Integrable ρ) : Integrable (packetDensity g ρ) := by
  let := fermiMeasure_finite ρ hp hm hi
  let : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
  exact ((frameDensity_integrable (packetState_toL2_memLp (complexWindow g)
    (phaseMeasure (fermiRadius ρ)))).const_mul 2).congr (fermiPacket_density g ρ hp hm hi)

lemma schwartz_square_le (g : 𝓢(Space,ℝ)) (x : Space) :
    g x^2 ≤ (SchwartzMap.seminorm ℝ 0 0 g)^2 := by
  have h := g.norm_le_seminorm ℝ x
  simpa only [Real.norm_eq_abs,sq_abs] using pow_le_pow_left₀ (norm_nonneg (g x)) h 2

lemma packetDensity_integrand_integrable (g : 𝓢(Space,ℝ)) (ρ : Space → ℝ)
    (hp : ∀ y, 0 ≤ ρ y) (hm : Measurable ρ) (hi : Integrable ρ) (x : Space) :
    Integrable (fun y => g (x-y)^2*ρ y) := by
  apply (hi.const_mul ((SchwartzMap.seminorm ℝ 0 0 g)^2)).mono'
    (((g.continuous.measurable.comp (measurable_const.sub measurable_id)).pow_const 2).mul hm).aestronglyMeasurable
  filter_upwards [] with y
  change ‖g (x-y)^2*ρ y‖ ≤ _
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (hp y))]
  exact mul_le_mul_of_nonneg_right (schwartz_square_le g _) (hp y)

lemma packetDensity_bound (g : 𝓢(Space,ℝ)) (ρ : Space → ℝ) (hp : ∀ y, 0 ≤ ρ y)
    (hm : Measurable ρ) (hi : Integrable ρ) (x : Space) :
    packetDensity g ρ x ≤ (SchwartzMap.seminorm ℝ 0 0 g)^2 * ∫ y, ρ y := by
  calc
    _ ≤ ∫ y, (SchwartzMap.seminorm ℝ 0 0 g)^2*ρ y :=
      integral_mono (packetDensity_integrand_integrable g ρ hp hm hi x)
        (hi.const_mul _) (fun y => mul_le_mul_of_nonneg_right (schwartz_square_le g _) (hp y))
    _ = _ := integral_const_mul _ _

lemma packetDensity_support (g : 𝓢(Space,ℝ)) (ρ : Space → ℝ) (K : Set Space)
    (hs : ∀ y, y ∉ K → ρ y = 0) (x : Space) (hx : x ∉ K + tsupport (g : Space → ℝ)) :
    packetDensity g ρ x = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [] with y
  by_cases hy : y ∈ K
  · have hxy : x-y ∉ tsupport (g : Space → ℝ) := by
      intro h
      apply hx
      exact ⟨y,hy,x-y,h,by abel_nf⟩
    rw [image_eq_zero_of_notMem_tsupport hxy]
    norm_num
  · simp only [hs y hy,mul_zero,Pi.zero_apply]

lemma complexWindow_tsupport (g : 𝓢(Space,ℝ)) :
    tsupport (complexWindow g : Space → ℂ) = tsupport (g : Space → ℝ) := by
  unfold tsupport
  congr 1
  ext x
  change (↑(g x) : ℂ) ≠ 0 ↔ g x ≠ 0
  exact not_congr Complex.ofReal_eq_zero

lemma complexWindow_compactSupport (g : 𝓢(Space,ℝ)) (hgc : HasCompactSupport (g : Space → ℝ)) :
    HasCompactSupport (complexWindow g : Space → ℂ) := by
  change IsCompact (tsupport (complexWindow g : Space → ℂ))
  rw [complexWindow_tsupport]
  exact hgc

lemma fermiPhase_center_mem (ρ : Space → ℝ) (K : Set Space) (hs : ∀ y, y ∉ K → ρ y = 0)
    (yp : Space × Space) (hyp : yp ∈ phaseRegion (fermiRadius ρ)) : yp.1 ∈ K := by
  by_contra hn
  have hzero : fermiRadius ρ yp.1 = 0 := by simp [fermiRadius,hs yp.1 hn]
  change ‖yp.2‖ < fermiRadius ρ yp.1 at hyp
  rw [hzero] at hyp
  exact (not_lt_of_ge (norm_nonneg _)) hyp

lemma fermiPhase_momentum_bound (ρ : Space → ℝ) (hp : ∀ y, 0 ≤ ρ y)
    (C : ℝ) (hC : ∀ y, ρ y ≤ C) (yp : Space × Space) (hyp : yp ∈ phaseRegion (fermiRadius ρ)) :
    ‖yp.2‖ ≤ (3/(8*Real.pi)*C)^(1/3:ℝ) := by
  apply (le_of_lt hyp).trans
  exact Real.rpow_le_rpow (mul_nonneg (by positivity) (hp _))
    (mul_le_mul_of_nonneg_left (hC _) (by positivity)) (by norm_num)
end Coulomb

open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise

end

end OAI
