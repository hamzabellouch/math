import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeGlobalGamma

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]

lemma continuous_kernel_le_of_measurable_tests (μ : Measure X) [IsFiniteMeasure μ]
    [μ.IsOpenPosMeasure] (K E M : X → X → ℝ)
    (hK : Continuous (fun p : X × X => K p.1 p.2))
    (hM : Continuous (fun p : X × X => M p.1 p.2))
    (hEm : AEStronglyMeasurable (fun p : X × X => E p.1 p.2) (μ.prod μ))
    (hE : ∀ x y, |E x y| ≤ M x y)
    (htest : ∀ φ ψ : X → ℝ, ContMDiff Model 𝓘(ℝ,ℝ) ∞ φ →
      ContMDiff Model 𝓘(ℝ,ℝ) ∞ ψ → (∀ x, 0 ≤ φ x) → (∀ y, 0 ≤ ψ y) →
      (∫ x, ∫ y, φ x*ψ y*K x y ∂μ ∂μ) = ∫ x, ∫ y, φ x*ψ y*E x y ∂μ ∂μ) :
    ∀ x y, K x y ≤ M x y := by
  apply continuous_kernel_le_of_smooth_tests μ K M hK hM
  intro φ ψ hφ hψ hp hq
  have hG : Continuous (fun p : X × X => φ p.1*ψ p.2) :=
    (hφ.continuous.comp continuous_fst).mul (hψ.continuous.comp continuous_snd)
  have hMi : Integrable (fun p : X × X => φ p.1*ψ p.2*M p.1 p.2) (μ.prod μ) :=
    (hG.mul hM).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hEi : Integrable (fun p : X × X => φ p.1*ψ p.2*E p.1 p.2) (μ.prod μ) := by
    apply hMi.mono' (hG.aestronglyMeasurable.mul hEm)
    filter_upwards [] with p
    simp only [Pi.mul_apply] at ⊢
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (mul_nonneg (hp p.1) (hq p.2))]
    exact mul_le_mul_of_nonneg_left (hE p.1 p.2) (mul_nonneg (hp p.1) (hq p.2))
  rw [htest φ ψ hφ hψ hp hq,← integral_prod _ hEi,← integral_prod _ hMi]
  apply integral_mono hEi hMi
  intro p
  exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hE p.1 p.2))
    (mul_nonneg (hp p.1) (hq p.2))

lemma continuous_kernel_abs_le_of_measurable_tests (μ : Measure X) [IsFiniteMeasure μ]
    [μ.IsOpenPosMeasure] (K E M : X → X → ℝ)
    (hK : Continuous (fun p : X × X => K p.1 p.2))
    (hM : Continuous (fun p : X × X => M p.1 p.2))
    (hEm : AEStronglyMeasurable (fun p : X × X => E p.1 p.2) (μ.prod μ))
    (hE : ∀ x y, |E x y| ≤ M x y)
    (htest : ∀ φ ψ : X → ℝ, ContMDiff Model 𝓘(ℝ,ℝ) ∞ φ →
      ContMDiff Model 𝓘(ℝ,ℝ) ∞ ψ → (∀ x, 0 ≤ φ x) → (∀ y, 0 ≤ ψ y) →
      (∫ x, ∫ y, φ x*ψ y*K x y ∂μ ∂μ) = ∫ x, ∫ y, φ x*ψ y*E x y ∂μ ∂μ) :
    ∀ x y, |K x y| ≤ M x y := by
  have hu := continuous_kernel_le_of_measurable_tests μ K E M hK hM hEm hE htest
  have hl := continuous_kernel_le_of_measurable_tests μ (fun x y => -K x y)
    (fun x y => -E x y) M hK.neg hM hEm.neg
    (fun x y => by simpa only [abs_neg] using hE x y) ?_
  · intro x y
    exact abs_le.mpr ⟨neg_le.mp (hl x y),hu x y⟩
  intro φ ψ hφ hψ hp hq
  simp_rw [mul_neg,integral_neg]
  exact congrArg Neg.neg (htest φ ψ hφ hψ hp hq)

open ManifoldLocalization ManifoldVolume
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

include hs ht in

lemma geometric_kernel_abs_le_of_measurable_tests (K E M : X → X → ℝ)
    (hK : Continuous (fun p : X × X => K p.1 p.2))
    (hM : Continuous (fun p : X × X => M p.1 p.2))
    (hEm : AEStronglyMeasurable (fun p : X × X => E p.1 p.2)
      ((geometricVolume A J α).prod (geometricVolume A J α)))
    (hE : ∀ x y, |E x y| ≤ M x y)
    (htest : ∀ φ ψ : X → ℝ, ContMDiff Model 𝓘(ℝ,ℝ) ∞ φ →
      ContMDiff Model 𝓘(ℝ,ℝ) ∞ ψ → (∀ x, 0 ≤ φ x) → (∀ y, 0 ≤ ψ y) →
      (∫ x, ∫ y, φ x*ψ y*K x y ∂geometricVolume A J α ∂geometricVolume A J α) =
        ∫ x, ∫ y, φ x*ψ y*E x y ∂geometricVolume A J α ∂geometricVolume A J α) :
    ∀ x y, |K x y| ≤ M x y := by
  let := geometricVolume_finite A J α hs ht
  let := geometricVolume_openPos A J α hs ht
  exact continuous_kernel_abs_le_of_measurable_tests (geometricVolume A J α) K E M hK hM hEm hE htest

end TamingCompatibility.GeometricHilbert

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.VolterraKernel
open MeasureTheory Set Filter VolterraBounds
variable {X B : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
  [BorelSpace X] [SecondCountableTopology X]
  [NormedRing B] [NormedAlgebra ℝ B] [CompleteSpace B]
variable (μ : Measure X) [IsFiniteMeasure μ]
variable (K L : Kernel (X := X) (B := B)) {T A C : ℝ}
  (hK : HeatBound μ 0 T A K) (hL : HeatBound μ 0 T C L)
include hK hL

omit [SecondCountableTopology X] [CompleteSpace B] [BorelSpace X] in
lemma spatial_continuous {t s : ℝ} (ht : t ∈ Ioc 0 T) (hs : s ∈ Ioo 0 t)
    (hKc : Continuous (fun p : X × X => K (t-s) p.1 p.2))
    (hLc : Continuous (fun p : X × X => L s p.1 p.2)) :
    Continuous (fun p : X × X => spatial μ K L t s p.1 p.2) := by
  have ha : t-s ∈ Ioc 0 T := ⟨sub_pos.mpr hs.2,(sub_le_self _ hs.1.le).trans ht.2⟩
  have hb : s ∈ Ioc 0 T := ⟨hs.1,hs.2.le.trans ht.2⟩
  change Continuous (fun p : X × X => ∫ z, K (t-s) p.1 z * L s z p.2 ∂μ)
  apply continuous_of_dominated
    (fun p : X × X => (product_section K L hK.measurable hL.measurable t s p.1 p.2).aestronglyMeasurable)
    (bound := fun _ => (A/(t-s)^2)*(C/s^2))
  · intro p
    filter_upwards [] with z
    have hk := hK.sup _ ha p.1 z
    have hl := hL.sup _ hb z p.2
    simp only [weight,pow_zero,one_mul] at hk hl
    exact (norm_mul_le _ _).trans (mul_le_mul hk hl (norm_nonneg _) (by have := hK.nonneg; positivity))
  · exact integrable_const _
  · filter_upwards [] with z
    exact (hKc.comp (continuous_fst.prodMk continuous_const)).mul
      (hLc.comp (continuous_const.prodMk continuous_snd))

omit [SecondCountableTopology X] [CompleteSpace B] [BorelSpace X] in
lemma convolution_continuous {t : ℝ} (ht : t ∈ Ioc 0 T)
    (hKc : ∀ u ∈ Ioc 0 T, Continuous (fun p : X × X => K u p.1 p.2))
    (hLc : ∀ u ∈ Ioc 0 T, Continuous (fun p : X × X => L u p.1 p.2)) :
    Continuous (fun p : X × X => convolution μ K L t p.1 p.2) := by
  have ha (s : ℝ) (hs : s ∈ Ioo 0 t) : t-s ∈ Ioc 0 T :=
    ⟨sub_pos.mpr hs.2,(sub_le_self _ hs.1.le).trans ht.2⟩
  have hb (s : ℝ) (hs : s ∈ Ioo 0 t) : s ∈ Ioc 0 T := ⟨hs.1,hs.2.le.trans ht.2⟩
  change Continuous (fun p : X × X => ∫ s in Ioo 0 t, spatial μ K L t s p.1 p.2)
  apply continuous_of_dominated
    (fun p : X × X => (spatial_section μ K L hK.measurable hL.measurable t p.1 p.2).aestronglyMeasurable)
    (bound := fun _ => 4*A*C/t^2)
  · intro p
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    have h := time_integrand_bound μ 0 ht.1 hs.1 hs.2 hK.nonneg hL.nonneg K L p.1 p.2
      (hK.sup _ (ha s hs) p.1) (fun z => hL.sup _ (hb s hs) z p.2)
      (hK.row_int _ (ha s hs) p.1) (hL.col_int _ (hb s hs) p.2)
      (hK.row _ (ha s hs) p.1) (hL.col _ (hb s hs) p.2)
      (product_section K L hK.measurable hL.measurable t s p.1 p.2).aestronglyMeasurable
    simpa only [weight,pow_zero,one_mul,spatial] using h.2
  · exact integrableOn_const (by simp)
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact spatial_continuous μ K L hK hL ht hs (hKc _ (ha s hs)) (hLc _ (hb s hs))

end TamingCompatibility.GeometricHilbert.VolterraKernel

namespace TamingCompatibility.GeometricHilbert.KernelSeries
open MeasureTheory Set Filter VolterraKernel VolterraBounds
variable {X B : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
  [BorelSpace X] [SecondCountableTopology X]
  [NormedRing B] [NormedAlgebra ℝ B] [CompleteSpace B]
variable (μ : Measure X) [IsFiniteMeasure μ]
variable (R : Kernel (X := X) (B := B)) {T A : ℝ} (hT : 0 ≤ T)
  (hR : HeatBound μ 0 T A R)
  (hRc : ∀ t ∈ Ioc 0 T, Continuous (fun p : X × X => R t p.1 p.2))
include hT hR hRc

omit [CompleteSpace B] in
lemma term_continuous (n : ℕ) :
    ∀ t ∈ Ioc 0 T, Continuous (fun p : X × X => term μ T R n t p.1 p.2) := by
  induction n with
  | zero =>
    intro t ht
    apply (continuous_neg.comp (hRc t ht)).congr
    intro p
    simp only [term,clip_of_mem T _ ht]
    rfl
  | succ n ih =>
    intro t ht
    apply (continuous_neg.comp
      (convolution_continuous μ R (term μ T R n) hR (term_heatBound μ 0 hT R hR n) ht hRc ih)).congr
    intro p
    simp only [term,clip_of_mem T _ ht]
    rfl

lemma correction_continuous (hq : 4*T*A < 1) {t : ℝ} (ht : t ∈ Ioc 0 T) :
    Continuous (fun p : X × X => correction μ T R t p.1 p.2) := by
  have hq0 : 0 ≤ 4*T*A := by have := hR.nonneg; positivity
  have hsum : Summable (fun n : ℕ => (A/t^2)*(4*T*A)^n) :=
    (summable_geometric_of_norm_lt_one (x := (4*T*A : ℝ)) (by rwa [Real.norm_of_nonneg hq0])).mul_left _
  apply continuous_tsum (fun n => term_continuous μ R hT hR hRc n t ht) hsum
  intro n p
  have h := (term_heatBound μ 0 hT R hR n).sup t ht p.1 p.2
  simp only [weight,pow_zero,one_mul] at h
  exact h.trans_eq (by ring)

end TamingCompatibility.GeometricHilbert.KernelSeries

end
end

end

end OAI
