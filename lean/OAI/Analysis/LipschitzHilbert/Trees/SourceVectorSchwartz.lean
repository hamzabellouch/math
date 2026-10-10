import OAI.Analysis.LipschitzHilbert.Trees.SourceVectorSlices
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

namespace OAI

/-! Finite scalar packet coordinates assemble into an actual vector
Schwartz function. Fourier cutoffs pass through the same coordinates. -/
noncomputable section
open MeasureTheory FourierTransform
open scoped BigOperators
namespace LipschitzHilbert
variable {κ : Type*} [Fintype κ]
attribute [local instance] Classical.propDecidable

def vectorCoordinate (k : κ) : EuclideanSpace ℂ κ →L[ℂ] ℂ :=
  PiLp.proj 2 (fun _ : κ => ℂ) k

omit [Fintype κ] in
@[simp] theorem vectorCoordinate_apply (k : κ) (v : EuclideanSpace ℂ κ) :
    vectorCoordinate k v=v k := rfl

def vectorCoordinateInjection (k : κ) : ℂ →L[ℂ] EuclideanSpace ℂ κ :=
  ContinuousLinearMap.toSpanSingleton ℂ (PiLp.single 2 k 1)

@[simp] theorem vectorCoordinateInjection_apply (k j : κ) (z : ℂ) :
    vectorCoordinateInjection k z j=if j=k then z else 0 := by
  classical
  simp only [vectorCoordinateInjection,ContinuousLinearMap.toSpanSingleton_apply,
    PiLp.smul_apply,PiLp.single_apply,smul_eq_mul]
  split_ifs <;> simp_all

def vectorSchwartz {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (f : κ → SchwartzMap D ℂ) : SchwartzMap D (EuclideanSpace ℂ κ) :=
  ∑ k, (f k).postcompCLM (vectorCoordinateInjection k)

@[simp] theorem vectorSchwartz_apply {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (f : κ → SchwartzMap D ℂ) (x : D) (k : κ) : vectorSchwartz f x k=f k x := by
  classical
  simp only [vectorSchwartz,sum_apply,SchwartzMap.postcompCLM_apply,WithLp.ofLp_sum,Finset.sum_apply,
    vectorCoordinateInjection_apply]
  simp

theorem vector_fourier_coordinate (f : SchwartzMap ℝ (EuclideanSpace ℂ κ))
    (k : κ) (ξ : ℝ) :
    (𝓕 f ξ) k=𝓕 (f.postcompCLM (vectorCoordinate k)) ξ := by
  let phase := fun x : ℝ => Real.fourierChar (-(x*ξ))
  have hi : Integrable (fun x => phase x • f x) := by
    apply f.integrable.norm.mono' (by fun_prop)
    filter_upwards [] with x
    simp only [Circle.norm_smul]
    exact le_rfl
  have h := (vectorCoordinate k).integral_comp_comm hi
  simp only [SchwartzMap.fourier_coe,Real.fourier_eq,Real.inner_apply]
  change vectorCoordinate k (∫ x, phase x • f x)=
    ∫ x, phase x • (f.postcompCLM (vectorCoordinate k)) x
  rw [←h]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [Circle.smul_def,map_smul,SchwartzMap.postcompCLM_apply]

theorem vectorSchwartz_fourier_coordinate (f : κ → SchwartzMap ℝ ℂ) (k : κ) (ξ : ℝ) :
    (𝓕 (vectorSchwartz f) ξ) k=𝓕 (f k) ξ := by
  have heq : (vectorSchwartz f).postcompCLM (vectorCoordinate k)=f k := by
    ext x
    simp only [SchwartzMap.postcompCLM_apply,vectorCoordinate_apply,vectorSchwartz_apply]
  rw [vector_fourier_coordinate,heq]

theorem vectorSchwartz_fourier_zero (f : κ → SchwartzMap ℝ ℂ) (ξ : ℝ)
    (hf : ∀ k, 𝓕 (f k) ξ=0) : 𝓕 (vectorSchwartz f) ξ=0 := by
  ext k
  rw [vectorSchwartz_fourier_coordinate,hf]
  rfl

end LipschitzHilbert

end

end OAI
