import Mathlib
import OAI.Analysis.CoulombRadii.Packets.PacketStateJointSquareIntegrable
import OAI.Analysis.CoulombRadii.FormDomain.SpaceFourierL2
import OAI.Analysis.CoulombRadii.FormDomain.ThomasFermiKineticConstant

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
namespace Coulomb
lemma fermiPacket_spectral_trace (g : 𝓢(Space,ℝ))
    (hg : (∫ x : Space, g x^2) = 1) (ρ : Space → ℝ) (hρ : ∀ y, 0 ≤ ρ y)
    (hm : Measurable ρ) (hI : Integrable ρ) :
    HasSum (fun i : Σ z, eigenspaceBasisSet (packetFrame (complexWindow g)
      (phaseMeasure (fermiRadius ρ))) z => 2*i.1.re) (∫ y : Space, ρ y) := by
  let := fermiMeasure_finite ρ hρ hm hI
  have hg' : (∫ x : Space, ‖complexWindow g x‖^2) = 1 := by
    simpa only [complexWindow_apply, Complex.norm_real, Real.norm_eq_abs, sq_abs] using hg
  have h := (packetFrame_spectral_trace (complexWindow g) hg' (phaseMeasure (fermiRadius ρ))).mul_left 2
  rw [measureReal_def, fermiMeasure_mass ρ hρ hm hI,
    ENNReal.toReal_ofReal (div_nonneg (integral_nonneg hρ) (by norm_num))] at h
  convert h using 1
  ring

lemma fermiPacket_density (g : 𝓢(Space,ℝ))
    (ρ : Space → ℝ) (hρ : ∀ y, 0 ≤ ρ y) (hm : Measurable ρ) (hI : Integrable ρ) :
    let μ := phaseMeasure (fermiRadius ρ)
    letI := fermiMeasure_finite ρ hρ hm hI
    (fun x : Space => 2 * frameDensity (packetState_toL2_memLp (complexWindow g) μ) x) =ᵐ[volume]
      (fun x : Space => ∫ y : Space, g (x-y)^2 * ρ y) := by
  dsimp only
  let := fermiMeasure_finite ρ hρ hm hI
  filter_upwards [packetFrame_density (complexWindow g) (phaseMeasure (fermiRadius ρ))] with x hx
  rw [hx]
  simp only [complexWindow_apply, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [fermiMeasure_center_integral ρ hρ hm (fun y => g (x-y)^2) (by fun_prop) (fun y => sq_nonneg _)]
  ring

lemma packet_momentum_basis_sum (p : Space) :
    (∑ d : Fin 3, (2*Real.pi*inner ℝ (EuclideanSpace.single d 1) p)^2) =
      (2*Real.pi)^2*‖p‖^2 := by
  simp only [EuclideanSpace.inner_single_left, conj_trivial, one_mul, mul_pow]
  rw [← Finset.mul_sum, EuclideanSpace.real_norm_sq_eq]

lemma fermiPacket_kinetic_trace (g : 𝓢(Space,ℝ))
    (hg : (∫ x : Space, g x^2) = 1) (ρ : Space → ℝ) (hρ : ∀ y, 0 ≤ ρ y)
    (hm : Measurable ρ) (hI : Integrable ρ) (hT : Integrable (fun y => ρ y^(5/3:ℝ))) :
    let μ := phaseMeasure (fermiRadius ρ)
    letI := fermiMeasure_finite ρ hρ hm hI
    let hv := packetState_toL2_memLp (complexWindow g) μ
    let b := compactSpectralBasis (packetFrame (complexWindow g) μ)
      (packetFrame_compact (complexWindow g) μ) (frameOperator_symmetric hv)
    HasSum (fun i : Σ z, eigenspaceBasisSet (packetFrame (complexWindow g) μ) z =>
      i.1.re * ∑ d : Fin 3, ∫ ξ : Space, (2*Real.pi*inner ℝ ξ (EuclideanSpace.single d 1))^2 *
        ‖(𝓕 (b i) : Lp ℂ 2 (volume : Measure Space)) ξ‖^2)
      (thomasFermiKineticConstant * (∫ y : Space, ρ y^(5/3:ℝ)) +
        (1/2:ℝ)*(∫ y : Space, ρ y) *
          ∑ d : Fin 3, ∫ x : Space, (fderiv ℝ g x (EuclideanSpace.single d 1))^2) := by
  dsimp only
  let μ := phaseMeasure (fermiRadius ρ)
  let := fermiMeasure_finite ρ hρ hm hI
  have hp := fermiMeasure_momentum_memLp ρ hρ hm hT
  have hs := hasSum_sum (s := (Finset.univ : Finset (Fin 3)))
    (fun d _ => (packetFrame_fourier_weighted_trace g μ hp (EuclideanSpace.single d 1)).2)
  simp only [← Finset.mul_sum, hg, mul_one] at hs
  have hi (d : Fin 3) : Integrable (fun yp : Space × Space =>
      (2*Real.pi*inner ℝ (EuclideanSpace.single d 1) yp.2)^2) μ := by
    have ha := hp.continuousLinearMap_comp ((2*Real.pi) • innerSL ℝ (EuclideanSpace.single d 1))
    simpa only [smul_apply, innerSL_apply_apply, smul_eq_mul,
      Function.comp_apply, Real.norm_eq_abs, sq_abs] using ha.integrable_norm_pow (by norm_num)
  have hmμ : μ.real univ = (∫ y : Space, ρ y)/2 := by
    rw [measureReal_def, fermiMeasure_mass ρ hρ hm hI,
      ENNReal.toReal_ofReal (div_nonneg (integral_nonneg hρ) (by norm_num))]
  have he : (∑ d : Fin 3, ∫ yp : Space × Space,
       (2*Real.pi*inner ℝ (EuclideanSpace.single d 1) yp.2)^2 +
         (∫ x : Space, (fderiv ℝ g x (EuclideanSpace.single d 1))^2) ∂μ) =
      thomasFermiKineticConstant * (∫ y : Space, ρ y^(5/3:ℝ)) +
        (1/2:ℝ)*(∫ y : Space, ρ y) *
          ∑ d : Fin 3, ∫ x : Space, (fderiv ℝ g x (EuclideanSpace.single d 1))^2 := by
    simp_rw [integral_add (hi _) (integrable_const _), integral_const, smul_eq_mul]
    rw [Finset.sum_add_distrib, ← integral_finsetSum _ (fun d _ => hi d),
      ← Finset.mul_sum]
    simp only [packet_momentum_basis_sum, integral_const_mul]
    rw [fermiMeasure_kinetic ρ hρ hm, hmμ]
    ring
  rw [he] at hs
  exact hs
end Coulomb

open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution

end

end OAI
