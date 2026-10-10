import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.FiberMap

namespace OAI


noncomputable section
namespace TamingCompatibility.HilbertSobolev
open MeasureTheory TemperedDistribution EuclideanSobolevOperators
open scoped SchwartzMap LineDeriv
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def matrixLowerH {ι κ : Type*} [Fintype ι] [Fintype κ] (n : ℕ)
    (b : ι → 𝓢(E,ℂ)) (L : ι → F →L[ℂ] F) (v : ι → E)
    (c : κ → 𝓢(E,ℂ)) (K : κ → F →L[ℂ] F) : H E F ((n:ℝ)+1) →L[ℂ] H E F n :=
  (∑ i, product n (b i) ∘L fiberOperator n (L i) ∘L derivative ((n:ℝ)+1) (v i)) +
  ∑ i, product n (c i) ∘L fiberOperator n (K i) ∘L inclusion (by linarith : (n:ℝ) ≤ n+1)

lemma matrixLowerH_spec {ι κ : Type*} [Fintype ι] [Fintype κ] (n : ℕ)
    (b : ι → 𝓢(E,ℂ)) (L : ι → F →L[ℂ] F) (v : ι → E)
    (c : κ → 𝓢(E,ℂ)) (K : κ → F →L[ℂ] F) (u : H E F ((n:ℝ)+1)) :
    toDistribution E F n (matrixLowerH n b L v c K u) =
      matrixLowerOrder b L v c K (toDistribution E F ((n:ℝ)+1) u) := by
  have hd (i : ι) : toDistribution E F n (derivative ((n:ℝ)+1) (v i) u) =
      ∂_{v i} (toDistribution E F ((n:ℝ)+1) u) := by
    have h := toDistribution_derivative ((n:ℝ)+1) (v i) u
    have he : (n:ℝ)+1-1=n := by ring
    rw [he] at h
    exact h
  simp only [matrixLowerH,matrixLowerOrder,add_apply,sum_apply,ContinuousLinearMap.comp_apply,
    map_add,map_sum,toDistribution_product,toDistribution_fiberOperator,
    hd,toDistribution_inclusion]

def secondCommutatorH (n : ℕ) (g : 𝓢(E,ℂ)) (v w : E) :
    H E F ((n:ℝ)+1) →L[ℂ] H E F n :=
  product n (∂_{v} (∂_{w} g) : 𝓢(E,ℂ)) ∘L inclusion (by linarith : (n:ℝ) ≤ n+1) +
  product n (∂_{w} g : 𝓢(E,ℂ)) ∘L derivative ((n:ℝ)+1) v +
  product n (∂_{v} g : 𝓢(E,ℂ)) ∘L derivative ((n:ℝ)+1) w

lemma secondCommutatorH_spec (n : ℕ) (g : 𝓢(E,ℂ)) (v w : E) (u : H E F ((n:ℝ)+1)) :
    toDistribution E F n (secondCommutatorH n g v w u) =
      secondCommutator g v w (toDistribution E F ((n:ℝ)+1) u) := by
  have hd (v : E) : toDistribution E F n (derivative ((n:ℝ)+1) v u) =
      ∂_{v} (toDistribution E F ((n:ℝ)+1) u) := by
    have h := toDistribution_derivative ((n:ℝ)+1) v u
    have he : (n:ℝ)+1-1=n := by ring
    rw [he] at h
    exact h
  simp only [secondCommutatorH,secondCommutator,add_apply,ContinuousLinearMap.comp_apply,
    map_add,toDistribution_product,hd,toDistribution_inclusion]

def localizationErrorH (n : ℕ) (a : basisIndex E → basisIndex E → 𝓢(E,ℂ))
    (g : 𝓢(E,ℂ)) : H E F ((n:ℝ)+1) →L[ℂ] H E F n :=
  -(((2*Real.pi)^2)⁻¹ : ℝ) • ∑ i, secondCommutatorH n g
    (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E i) +
  ∑ i, ∑ j, product n (a i j) ∘L secondCommutatorH n g
    (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E j)

lemma localizationErrorH_spec (n : ℕ) (a : basisIndex E → basisIndex E → 𝓢(E,ℂ))
    (g : 𝓢(E,ℂ)) (u : H E F ((n:ℝ)+1)) :
    toDistribution E F n (localizationErrorH n a g u) =
      localizationError a g (toDistribution E F ((n:ℝ)+1) u) := by
  simp only [localizationErrorH,localizationError,add_apply,smul_apply,sum_apply,
    ContinuousLinearMap.comp_apply,map_add,map_sum,ContinuousLinearMap.map_smul_of_tower,
    toDistribution_product,secondCommutatorH_spec]

lemma perturbedHelmholtz_half_bound (n : ℕ)
    (a : basisIndex E → basisIndex E → 𝓢(E,ℂ))
    (ha : ‖perturbation (F := F) n a‖ ≤ 1/2)
    (u : H E F ((n:ℝ)+2)) (f : H E F n)
    (heq : perturbedHelmholtz a (toDistribution E F ((n:ℝ)+2) u) = toDistribution E F n f) :
    ‖u‖ ≤ 2 * ‖f‖ := by
  rw [perturbedHelmholtz_toDistribution] at heq
  have he := toDistribution_injective (n:ℝ) heq
  have hpert := (perturbation n a).le_opNorm u
  have hhalf := mul_le_mul_of_nonneg_right ha (norm_nonneg u)
  have hn := norm_add_le f (-perturbation n a u)
  have hu : f + (-perturbation n a u) = u := by rw [← he]; abel
  rw [hu,norm_neg] at hn
  nlinarith
end TamingCompatibility.HilbertSobolev

end

end OAI
