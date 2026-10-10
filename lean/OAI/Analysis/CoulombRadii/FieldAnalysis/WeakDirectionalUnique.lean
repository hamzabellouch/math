import Mathlib

namespace OAI

section
section
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
noncomputable section
namespace Coulomb
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma weak_directional_unique {f d e : E → ℂ} (a : E)
    (hd : LocallyIntegrable d volume) (he : LocallyIntegrable e volume)
    (hfd : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, (fderiv ℝ φ x a : ℂ)*f x) = -(∫ x, (φ x : ℂ)*d x))
    (hfe : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, (fderiv ℝ φ x a : ℂ)*f x) = -(∫ x, (φ x : ℂ)*e x)) :
    d =ᵐ[volume] e := by
  apply ae_eq_of_integral_contDiff_smul_eq hd he
  intro φ hφ hφC
  simpa only [← Complex.real_smul, neg_inj] using (hfd φ hφ hφC).symm.trans (hfe φ hφ hφC)

lemma weak_directional_zero_on_open {f d : E → ℂ} (a : E)
    (hd : LocallyIntegrable d volume)
    (hfd : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, (fderiv ℝ φ x a : ℂ)*f x) = -(∫ x, (φ x : ℂ)*d x))
    (U : Set E) (hU : IsOpen U) (hfU : ∀ᵐ x ∂volume, x ∈ U → f x = 0) :
    ∀ᵐ x ∂volume, x ∈ U → d x = 0 := by
  apply hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hd.locallyIntegrableOn U)
  intro φ hφ hφC hφU
  have hzero : (∫ x, (fderiv ℝ φ x a : ℂ)*f x) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hfU] with x hx
    by_cases h : x ∈ U
    · simp [hx h]
    · have hn : x ∉ tsupport φ := fun hh => h (hφU hh)
      simp [fderiv_of_notMem_tsupport ℝ hn]
  have H := hfd φ hφ hφC
  rw [hzero] at H
  simpa only [← Complex.real_smul, neg_eq_zero] using H.symm

lemma smooth_compact_weak_directional (f : E → ℂ)
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (a : E)
    (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    (∫ x, (fderiv ℝ φ x a : ℂ)*f x) =
      -(∫ x, (φ x : ℂ)*fderiv ℝ f x a) := by
  let g : E → ℂ := fun x => (φ x : ℂ)
  have hg : ContDiff ℝ ∞ g := Complex.ofRealCLM.contDiff.comp hφ
  have hgc : HasCompactSupport g := hφc.comp_left Complex.ofReal_zero
  have hd (x : E) : fderiv ℝ g x a = (fderiv ℝ φ x a : ℂ) := by
    exact congrArg (fun L : E →L[ℝ] ℂ => L a)
      ((Complex.ofRealCLM.hasFDerivAt.comp x
        ((hφ.differentiable (by simp)) x).hasFDerivAt).fderiv)
  have hdf : Continuous (fun x => fderiv ℝ f x a) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdg : Continuous (fun x => fderiv ℝ g x a) :=
    (hg.continuous_fderiv (by simp)).clm_apply continuous_const
  have h1 : Integrable (fun x => fderiv ℝ g x a*f x) :=
    (hdg.mul hf.continuous).integrable_of_hasCompactSupport hfc.mul_left
  have h2 : Integrable (fun x => g x*fderiv ℝ f x a) :=
    (hg.continuous.mul hdf).integrable_of_hasCompactSupport hgc.mul_right
  have h3 : Integrable (fun x => g x*f x) :=
    (hg.continuous.mul hf.continuous).integrable_of_hasCompactSupport hgc.mul_right
  have H := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h1 h2 h3
    (fun x _ => hg.differentiable (by simp) x)
    (fun x _ => hf.differentiable (by simp) x)
  simpa only [hd, g] using (neg_eq_iff_eq_neg.mp H.symm)

lemma weak_directional_eq_smooth {u d : Lp ℂ 2 (volume : Measure E)}
    (a : E) (F : E → ℂ) (hFs : ContDiff ℝ ∞ F) (hFc : HasCompactSupport F)
    (hu : (u : E → ℂ) =ᵐ[volume] F)
    (hd : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, (fderiv ℝ φ x a : ℂ)*u x) = -(∫ x, (φ x : ℂ)*d x)) :
    (d : E → ℂ) =ᵐ[volume] fun x => fderiv ℝ F x a := by
  apply weak_directional_unique (f := F) a
    ((Lp.memLp d).locallyIntegrable (by norm_num))
    (((hFs.continuous_fderiv (by simp)).clm_apply continuous_const).locallyIntegrable)
  · intro φ hφ hφC
    rw [← hd φ hφ hφC]
    apply integral_congr_ae
    filter_upwards [hu] with x hx
    rw [hx]
  · exact smooth_compact_weak_directional F hFs hFc a

lemma weak_directional_smooth_norm_sq {u d : Lp ℂ 2 (volume : Measure E)}
    (a : E) (F : E → ℂ) (hFs : ContDiff ℝ ∞ F) (hFc : HasCompactSupport F)
    (hu : (u : E → ℂ) =ᵐ[volume] F)
    (hd : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, (fderiv ℝ φ x a : ℂ)*u x) = -(∫ x, (φ x : ℂ)*d x)) :
    (∫ x, ‖fderiv ℝ F x a‖^2) = ‖d‖^2 := by
  have he := weak_directional_eq_smooth a F hFs hFc hu hd
  calc
    _ = ∫ x, ‖d x‖^2 := integral_congr_ae (he.mono (fun x hx => by dsimp only at hx ⊢; rw [hx]))
    _ = ‖d‖^2 := by
      apply Complex.ofReal_injective
      rw [← integral_complex_ofReal]
      calc
        _ = inner ℂ d d := by
          rw [L2.inner_def]
          apply integral_congr_ae
          filter_upwards [] with x
          simp [inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]
        _ = _ := by simp [inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]
end Coulomb

end
end
end

end OAI
