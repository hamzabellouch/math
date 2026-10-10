import Mathlib
import OAI.Probability.SKBarriers.Scalar.PrefixAlgebra

namespace OAI

section

section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem hierarchyMomentLevel_fixed_family {I : Type} (n : ℕ) (m : Fin n → ℝ)
    (f : ParameterSpace n → ℝ) (g : I → ParameterSpace n → ℝ)
    (hf : BoundedDerivs f) (j : Fin (n+1))
    (hg : ∀ i, hierarchyMomentLevel n m f (g i) j = g i) (F : (I → ℝ) → ℝ) :
    hierarchyMomentLevel n m f (fun z => F (fun i => g i z)) j = fun z => F (fun i => g i z) := by
  have H := hierarchyMomentLevel_family n m f g hf F j
  simpa only [hg] using H

theorem hierarchyMomentLevel_fixed_mul (n : ℕ) (m : Fin n → ℝ)
    (f g h : ParameterSpace n → ℝ) (hf : BoundedDerivs f) (j : Fin (n+1))
    (hg : hierarchyMomentLevel n m f g j = g) (hh : hierarchyMomentLevel n m f h j = h) :
    hierarchyMomentLevel n m f (fun z => g z*h z) j = fun z => g z*h z := by
  let G : Bool → ParameterSpace n → ℝ := fun b => if b then g else h
  have hr (b : Bool) : hierarchyMomentLevel n m f (G b) j = G b := by
    cases b <;> assumption
  exact hierarchyMomentLevel_fixed_family n m f G hf j hr (fun a => a true*a false)

section SharedSpinTest
variable {S : Type} [Fintype S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]

theorem hierarchyGaussian_integrable (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (g : S → ParameterSpace n → ℝ)
    (hg : ∀ s, HasExpGrowth (g s)) (hc : ∀ s, Continuous (g s)) :
    Integrable (fun sz => g sz.1 sz.2) (hierarchyGaussianLaw n m U) := by
  rw [hierarchyGaussianLaw_eq_spinGaussian]
  exact spinGaussian_integrable n _ g (hierarchyPotential_boundedDerivs n m U) hg hc

theorem hierarchyGaussian_memLp_two (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (g : S → ParameterSpace n → ℝ)
    (hg : ∀ s, HasExpGrowth (g s)) (hc : ∀ s, Continuous (g s)) :
    MemLp (fun sz => g sz.1 sz.2) 2 (hierarchyGaussianLaw n m U) := by
  have hI := hierarchyGaussian_integrable n m U g hg hc
  rw [memLp_two_iff_integrable_sq hI.aestronglyMeasurable]
  simpa only [pow_two] using hierarchyGaussian_integrable n m U (fun s z => g s z*g s z)
    (fun s => (hg s).mul (hg s)) (fun s => (hc s).mul (hc s))

omit [MeasurableSpace S] [MeasurableSingletonClass S] in

theorem hierarchyLevel_shared_gradient (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (c : S → ℝ) (j : Fin (n+1))
    (u v : ParameterSpace n) (hu : TailZero n j u) (hv : PrefixZero n j v)
    (hU : ∀ s, U s u = c s) (z : ParameterSpace n) :
    fderiv ℝ (hierarchyLevel n m (affineLogPartition (fun _ => 0) U) j) z (u+v) =
      hierarchySpinMean n m U c j z := by
  rw [map_add]
  have H := (hierarchyLevel_invariant_of_prefix n m _ v j hv).fderiv_zero
    ((hierarchyLevel_boundedDerivs n m _ (affineLogPartition_boundedDerivs (fun _ => 0) U) j).1.differentiable (by norm_num)) z
  rw [H,add_zero]
  exact congrFun (hierarchyLevel_spinMean n m U c j u hu hU) z

theorem hierarchyGaussian_retained_stein (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (c : S → ℝ) (h : ParameterSpace n → ℝ)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hc : ∀ s, ‖c s‖ ≤ C) (hb : ∀ z, ‖h z‖ ≤ D)
    (hcont : ContDiff ℝ 1 h) (hdh : HasExpGrowth (fderiv ℝ h))
    (a : Fin n → ℝ) (j l : Fin (n+1)) (hjl : j ≤ l)
    (u v : ParameterSpace n) (ha : coordinateVector n a = u+v)
    (hu : TailZero n j u) (hv : PrefixZero n j v) (huc : ∀ s, U s u = c s)
    (hU : ∀ s, U s (coordinateVector n a) = 0)
    (hi : ∀ k, k ≠ j → hierarchyAtom n m 1 k = 0 ∨
      TranslationInvariant (hierarchyLevel n m (affineLogPartition (fun _ => 0) U) k) (coordinateVector n a))
    (hih : TranslationInvariant h (coordinateVector n a))
    (hf : hierarchyMomentLevel n m (affineLogPartition (fun _ => 0) U) h l = h) :
    (∫ sz, coordinateLinear n a sz.2*(c sz.1*h sz.2) ∂hierarchyGaussianLaw n m U) =
      -hierarchyAtom n m 1 j * ∫ z,
        (hierarchySpinMean n m U c j z*hierarchySpinMean n m U c l z)*h z
          ∂hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) 0 := by
  let f := affineLogPartition (fun _ => 0) U
  have hfr := affineLogPartition_boundedDerivs (fun _ => 0) U
  have hgb := HasExpGrowth.of_bounded hD hb
  have hs := hierarchyGaussian_shared_stein n m U (fun s z => c s*h z)
    (fun _ => contDiff_const.mul hcont)
    (fun s => (HasExpGrowth.const (c s)).mul hgb)
    (fun s => by
      have he : fderiv ℝ (fun z : ParameterSpace n => c s*h z) =
          fun z => c s • fderiv ℝ h z := by
        funext z
        exact ((hcont.differentiable (by norm_num) z).hasFDerivAt.const_mul (c s)).fderiv
      rw [he]
      exact (HasExpGrowth.const (c s)).smul hdh)
    a j hU hi (fun s z t => congrArg (fun r => c s*r) (hih z t))
  have Hder (z : ParameterSpace n) : fderiv ℝ (hierarchyLevel n m f j) z (coordinateVector n a) =
      hierarchySpinMean n m U c j z := by
    rw [ha]
    exact hierarchyLevel_shared_gradient n m U c j u v hu hv huc z
  dsimp only [f] at Hder
  simp_rw [Hder] at hs
  rw [hs]
  congr 1
  let A := hierarchySpinMean n m U c j
  let B := hierarchySpinMean n m U c l
  have hA := hierarchySpinMean_regular n m U c hC hc j
  have hB := hierarchySpinMean_regular n m U c hC hc l
  have hAc : Continuous A := hA.1
  have hAb : ∀ z, ‖A z‖ ≤ C := hA.2
  have hhp : ∀ z, ‖h z*A z‖ ≤ D*C := by
    intro z
    rw [norm_mul]
    exact mul_le_mul (hb z) (hAb z) (norm_nonneg _) hD
  have hfixA : hierarchyMomentLevel n m f A l = A :=
    hierarchyMomentLevel_retained n m f _ hfr j l hjl
  have hfix := hierarchyMomentLevel_fixed_mul n m f h A hfr l hf hfixA
  have hmarg := hierarchyGaussian_terminal_marginal n m U c (fun z => h z*A z)
    (hcont.continuous.mul hAc) (hgb.mul (HasExpGrowth.of_bounded hC hAb))
  have ht := hierarchyPathLaw_fixed_mul n m f (affineMoment (fun _ => 0) U c)
    (fun z => h z*A z) hfr (affineMoment_continuous (fun _ => 0) U c)
    (hcont.continuous.mul hAc) hC (mul_nonneg hD hC)
    (affineMoment_norm_le (fun _ => 0) U c hc) hhp l hfix 0
  calc
    _ = ∫ sz, c sz.1*(h sz.2*A sz.2) ∂hierarchyGaussianLaw n m U := by
      apply integral_congr_ae
      filter_upwards [] with sz
      ring
    _ = ∫ z, affineMoment (fun _ => 0) U c z*(h z*A z) ∂hierarchyPathLaw n m f 0 := hmarg
    _ = ∫ z, (h z*A z)*affineMoment (fun _ => 0) U c z ∂hierarchyPathLaw n m f 0 := by
      apply integral_congr_ae
      filter_upwards [] with z
      ring
    _ = ∫ z, (h z*A z)*B z ∂hierarchyPathLaw n m f 0 := ht
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with z
      ring
end SharedSpinTest
end SK.Analytic

end
end

end

end OAI
