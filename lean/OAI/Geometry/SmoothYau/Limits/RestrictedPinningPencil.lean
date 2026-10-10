import Mathlib
import OAI.Geometry.SmoothYau.Geometry.SymmetricFormsNondegenerate
import OAI.Geometry.SmoothYau.NodalMeasure.PositiveIntegral
import OAI.Geometry.SmoothYau.Smoothness.PinningTensorSpace
import OAI.Geometry.SmoothYau.Spectrum.AnnularOrthogonalTransverseNonzero
import OAI.Geometry.SmoothYau.Spectrum.ContinuousEigenpairLinearization

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T2Space M]
namespace MetricIntegralAtlas
variable (I : MetricIntegralAtlas (E := E) (M := M)) (g : SmoothMetric E M)
omit [T2Space M] in
lemma mean_add (f h : M → ℝ) (hf : Continuous f) (hh : Continuous h) :
    I.mean g (fun x => f x+h x) = I.mean g f+I.mean g h := by
  let F := BoundedContinuousFunction.mkOfCompact ⟨f,hf⟩
  let H := BoundedContinuousFunction.mkOfCompact ⟨h,hh⟩
  change I.integralCLM g (F+H) = I.integralCLM g F+I.integralCLM g H
  exact map_add _ _ _
end MetricIntegralAtlas
variable (I : MetricIntegralAtlas (E := E) (M := M)) (g : SmoothMetric E M)
variable {u : M → ℝ} {U : Set M}

def pinningEnergyBilin (K : pinningTensorSpace g u U) :
    LinearMap.BilinForm ℝ (RealSmoothFunctions E M) :=
  LinearMap.mk₂ ℝ (fun a b => I.mean g (fun x =>
      g.inner x (smoothMetricGradientLM g x a) (K.val x (smoothMetricGradientLM g x b))))
    (by
      intro a b c
      simp only [map_add]
      refine Eq.trans ?_ (I.mean_add g _ _
        (contMDiff_tensorEnergy g K.val K.property.1 a.contMDiff c.contMDiff).continuous
        (contMDiff_tensorEnergy g K.val K.property.1 b.contMDiff c.contMDiff).continuous)
      apply congrArg (I.mean g)
      funext x
      exact congrArg (fun L : E →L[ℝ] ℝ => L (K.val x (smoothMetricGradientLM g x c)))
        ((show E →L[ℝ] E →L[ℝ] ℝ from g.inner x).map_add
          (smoothMetricGradientLM g x a) (smoothMetricGradientLM g x b)))
    (by
      intro r a b
      simp only [map_smul]
      refine Eq.trans ?_ (I.mean_const_mul g r _
        (contMDiff_tensorEnergy g K.val K.property.1 a.contMDiff b.contMDiff).continuous)
      apply congrArg (I.mean g)
      funext x
      exact congrArg (fun L : E →L[ℝ] ℝ => L (K.val x (smoothMetricGradientLM g x b)))
        ((show E →L[ℝ] E →L[ℝ] ℝ from g.inner x).map_smul r (smoothMetricGradientLM g x a)))
    (by
      intro a b c
      simp only [map_add]
      refine Eq.trans ?_ (I.mean_add g _ _
        (contMDiff_tensorEnergy g K.val K.property.1 a.contMDiff b.contMDiff).continuous
        (contMDiff_tensorEnergy g K.val K.property.1 a.contMDiff c.contMDiff).continuous)
      apply congrArg (I.mean g)
      funext x
      let L : E →L[ℝ] ℝ := (show E →L[ℝ] ℝ from g.inner x (smoothMetricGradientLM g x a)).comp
        (show E →L[ℝ] E from K.val x)
      exact L.map_add (smoothMetricGradientLM g x b) (smoothMetricGradientLM g x c))
    (by
      intro r a b
      simp only [map_smul]
      refine Eq.trans ?_ (I.mean_const_mul g r _
        (contMDiff_tensorEnergy g K.val K.property.1 a.contMDiff b.contMDiff).continuous)
      apply congrArg (I.mean g)
      funext x
      let L : E →L[ℝ] ℝ := (show E →L[ℝ] ℝ from g.inner x (smoothMetricGradientLM g x a)).comp
        (show E →L[ℝ] E from K.val x)
      exact L.map_smul r (smoothMetricGradientLM g x b))

omit [T2Space M] in
lemma pinningEnergyBilin_apply (K : pinningTensorSpace g u U)
    (a b : RealSmoothFunctions E M) :
    pinningEnergyBilin I g K a b = I.mean g (fun x =>
      g.inner x (metricGradient g a x) (K.val x (metricGradient g b x))) := rfl

def pinningEnergyPencil : pinningTensorSpace g u U →ₗ[ℝ]
    LinearMap.BilinForm ℝ (RealSmoothFunctions E M) where
  toFun := pinningEnergyBilin I g
  map_add' K L := by
    ext a b
    change I.mean g (fun x => g.inner x (metricGradient g a x)
      ((K.val+L.val) x (metricGradient g b x))) = _
    simp only [Pi.add_apply,add_apply,map_add]
    exact I.mean_add g _ _
      (contMDiff_tensorEnergy g K.val K.property.1 a.contMDiff b.contMDiff).continuous
      (contMDiff_tensorEnergy g L.val L.property.1 a.contMDiff b.contMDiff).continuous
  map_smul' r K := by
    ext a b
    change I.mean g (fun x => g.inner x (metricGradient g a x)
      ((r • K.val) x (metricGradient g b x))) = _
    simp only [Pi.smul_apply,smul_apply,map_smul,smul_eq_mul]
    exact I.mean_const_mul g r _
      (contMDiff_tensorEnergy g K.val K.property.1 a.contMDiff b.contMDiff).continuous

omit [T2Space M] in
lemma pinningEnergyPencil_symmetric (K : pinningTensorSpace g u U)
    (a b : RealSmoothFunctions E M) :
    pinningEnergyPencil I g K a b = pinningEnergyPencil I g K b a := by
  change I.mean g _ = I.mean g _
  congr 1
  funext x
  exact (g.symm x _ _).trans (K.property.2.1 x _ _)
end


open Set Filter Function Manifold Bundle MeasureTheory
open scoped Topology ContDiff BoundedContinuousFunction
variable {W : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]

def restrictedPinningPencil
    {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
    [CompactSpace M] [T2Space M]
    (I : MetricIntegralAtlas (E := E) (M := M)) (g : SmoothMetric E M)
    {u : M → ℝ} {U : Set M} (σ : W →ₗ[ℝ] RealSmoothFunctions E M) :
    pinningTensorSpace g u U →ₗ[ℝ] LinearMap.BilinForm ℝ W where
  toFun K := (pinningEnergyPencil I g K).comp σ σ
  map_add' K L := by
    ext a b
    change pinningEnergyPencil I g (K+L) (σ a) (σ b) = _
    rw [map_add]
    rfl
  map_smul' r K := by
    ext a b
    change pinningEnergyPencil I g (r • K) (σ a) (σ b) = _
    rw [map_smul]
    rfl

theorem annular_nondegenerate_pinning_tensor
    (I : MetricIntegralAtlas (E := Euclidean 3) (M := Sphere 3))
    (g : SmoothMetric (Euclidean 3) (Sphere 3))
    (a b c : Euclidean 4)
    (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hc : inner ℝ c c = 1)
    (hab : inner ℝ a b = 0) (hac : inner ℝ a c = 0) (hbc : inner ℝ b c = 0)
    (n : ℕ) (hn : 2 ≤ n) {l h : ℝ} (hl : 0 < l) (hlh : l < h) (hh : h < 1)
    (u : RealSmoothFunctions (Euclidean 3) (Sphere 3))
    (hue : ∀ p, -laplaceBeltrami g u p = ((n:ℝ)*((n:ℝ)+2))*u p)
    (hup : ∀ p : Sphere 3, l < Complex.normSq (planarLinear a b p) →
      Complex.normSq (planarLinear a b p) < h → u p = roundPower a b n p)
    (hgp : ∀ p : Sphere 3, l < Complex.normSq (planarLinear a b p) →
      Complex.normSq (planarLinear a b p) < h →
      ∀ (X Y : TangentSpace 𝓘(ℝ,Euclidean 3) p),
        g.inner p X Y = (inner ℝ : Euclidean 4 → Euclidean 4 → ℝ)
          (mfderiv 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,Euclidean 4)
            (fun q : Sphere 3 => (q : Euclidean 4)) p X)
          (mfderiv 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,Euclidean 4)
            (fun q : Sphere 3 => (q : Euclidean 4)) p Y))
    (σ : W →ₗ[ℝ] RealSmoothFunctions (Euclidean 3) (Sphere 3))
    (hσ : Injective σ)
    (hσe : ∀ w p, -laplaceBeltrami g (σ w) p = ((n:ℝ)*((n:ℝ)+2))*σ w p)
    (hσo : ∀ w, I.mean g (fun x => σ w x*u x) = 0) :
    ∃ K : pinningTensorSpace g (u : Sphere 3 → ℝ)
      {p | l < Complex.normSq (planarLinear a b p) ∧ Complex.normSq (planarLinear a b p) < h},
      (restrictedPinningPencil I g σ K).Nondegenerate := by
  let : PreconnectedSpace (Sphere 3) := Subtype.preconnectedSpace
    (isPreconnected_sphere (by
      rw [← Module.finrank_eq_rank]
      norm_num [Euclidean,finrank_euclideanSpace]) (0 : Euclidean 4) 1)
  apply symmetric_forms_nondegenerate (restrictedPinningPencil I g σ)
  · intro K v w
    exact pinningEnergyPencil_symmetric I g K (σ v) (σ w)
  · intro w hw
    have hv : (σ w : Sphere 3 → ℝ) ≠ 0 := by
      intro hz
      apply hw
      apply hσ
      rw [map_zero]
      exact DFunLike.ext _ _ (congrFun hz)
    have ho : ∫ x, σ w x*u x ∂I.volumeMeasure g = 0 := by
      exact (I.mean_eq_volumeIntegral g (fun x => σ w x*u x)
        ((σ w).contMDiff.continuous.mul u.contMDiff.continuous)).symm.trans (hσo w)
    obtain ⟨χ,hχ,hK,htr,hku,hpos⟩ := annular_eigenfunction_separating_tensor
      (I.volumeMeasure g) g a b c ha hb hc hab hac hbc n hn hl hlh hh u.contMDiff
      (σ w).contMDiff hue (hσe w) hup hgp hv ho rfl
    let K : pinningTensorSpace g (u : Sphere 3 → ℝ)
        {p | l < Complex.normSq (planarLinear a b p) ∧ Complex.normSq (planarLinear a b p) < h} :=
      ⟨supportedPinningTensor g u (σ w) χ,
        hK, supportedPinningTensor_selfAdjoint g u (σ w) χ,htr,hku,by
          intro x hx
          apply supportedPinningTensor_zero
          by_contra hn
          exact hx (hχ (subset_tsupport _ hn))⟩
    refine ⟨K,ne_of_gt ?_⟩
    change 0 < I.mean g (fun x => g.inner x (metricGradient g (σ w) x)
      (supportedPinningTensor g u (σ w) χ x (metricGradient g (σ w) x)))
    rw [I.mean_eq_volumeIntegral g _
      (contMDiff_tensorEnergy g _ hK (σ w).contMDiff (σ w).contMDiff).continuous]
    exact hpos

end YauCounterexamples
end

end OAI
