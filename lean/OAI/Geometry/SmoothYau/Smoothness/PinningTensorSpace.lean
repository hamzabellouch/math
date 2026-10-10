import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.PulledGradient

namespace OAI

noncomputable section
open Set Filter Function Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction
namespace YauCounterexamples
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

def pinningTensorSpace (g : SmoothMetric E M) (u : M → ℝ) (U : Set M) :
    Submodule ℝ (∀ x : M, TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x) where
  carrier := {K | ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E) x (K x)) ∧
    (∀ x a b, g.inner x (K x a) b = g.inner x a (K x b)) ∧
    (∀ x, LinearMap.trace ℝ E (show E →L[ℝ] E from K x).toLinearMap = 0) ∧
    (∀ x, K x (metricGradient g u x) = 0) ∧ (∀ x, x ∉ U → K x = 0)}
  zero_mem' := by
    refine ⟨contMDiff_zeroSection ℝ _,?_,?_,?_,?_⟩
    · intros; simp
    · intro x
      change LinearMap.trace ℝ E (0 : E →ₗ[ℝ] E) = 0
      exact map_zero _
    · intros; simp
    · intros; rfl
  add_mem' := by
    rintro K L ⟨hK,hKs,hKt,hKu,hKU⟩ ⟨hL,hLs,hLt,hLu,hLU⟩
    refine ⟨hK.add_section hL,?_,?_,?_,?_⟩
    · intro x a b
      simp only [Pi.add_apply,add_apply,map_add,hKs,hLs]
    · intro x
      change LinearMap.trace ℝ E ((show E →L[ℝ] E from K x).toLinearMap +
        (show E →L[ℝ] E from L x).toLinearMap) = 0
      rw [map_add,hKt,hLt,add_zero]
    · intro x
      simp only [Pi.add_apply,add_apply,hKu,hLu,add_zero]
    · intro x hx
      simp only [Pi.add_apply,hKU x hx,hLU x hx,add_zero]
  smul_mem' := by
    rintro c K ⟨hK,hKs,hKt,hKu,hKU⟩
    refine ⟨contMDiff_const.smul_section hK,?_,?_,?_,?_⟩
    · intro x a b
      simp only [Pi.smul_apply,smul_apply,map_smul,hKs]
    · intro x
      change LinearMap.trace ℝ E (c • (show E →L[ℝ] E from K x).toLinearMap) = 0
      rw [map_smul,hKt,smul_zero]
    · intro x
      simp only [Pi.smul_apply,smul_apply,hKu,smul_zero]
    · intro x hx
      simp only [Pi.smul_apply,hKU x hx,smul_zero]

abbrev RealSmoothFunctions (E M : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] := C^∞⟮𝓘(ℝ,E),M;𝓘(ℝ,ℝ),ℝ⟯

def smoothMetricGradientLM (g : SmoothMetric E M) (x : M) :
    RealSmoothFunctions E M →ₗ[ℝ] E where
  toFun u := metricGradient g u x
  map_add' u v := by
    symm
    apply metricGradient_unique
    intro w
    change g.inner x (metricGradient g u x + metricGradient g v x) w =
      mfderiv 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ((u : M → ℝ)+(v : M → ℝ)) x w
    rw [mfderiv_add (u.contMDiff.mdifferentiable (by simp) x)
      (v.contMDiff.mdifferentiable (by simp) x)]
    simp only [map_add,add_apply,metricGradient_pairing]
    rfl
  map_smul' c u := by
    symm
    apply metricGradient_unique
    intro w
    have hh := ((u.contMDiff.mdifferentiable (by simp) x).hasMFDerivAt.const_smul c).mfderiv
    change g.inner x (c • metricGradient g u x) w =
      mfderiv 𝓘(ℝ,E) 𝓘(ℝ,ℝ) (c • (u : M → ℝ)) x w
    rw [hh]
    simp only [map_smul,smul_apply,metricGradient_pairing]
    rfl

lemma contMDiff_tensorEnergy (g : SmoothMetric E M)
    (K : ∀ x : M, TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x)
    (hK : ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E) x (K x)))
    {u v : M → ℝ} (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u)
    (hv : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ v) :
    ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞
      (fun x => g.inner x (metricGradient g u x) (K x (metricGradient g v x))) := by
  intro x
  have hh := (g.contMDiff x).clm_bundle_apply₂ (F₃ := ℝ) (E₃ := fun _ : M => ℝ)
    (contMDiff_metricGradient g hu x) ((hK x).clm_bundle_apply (contMDiff_metricGradient g hv x))
  rw [contMDiffAt_totalSpace] at hh
  exact hh.2
end YauCounterexamples
end

end OAI
