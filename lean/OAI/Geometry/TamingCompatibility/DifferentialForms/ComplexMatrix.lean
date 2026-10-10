import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.FiberMap

namespace OAI


noncomputable section
namespace TamingCompatibility.ComplexMatrix
open EuclideanSobolevOperators HilbertSobolev TemperedDistribution MeasureTheory LineDeriv
open scoped SchwartzMap LineDeriv
abbrev R (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev C (n : ℕ) := EuclideanSpace ℂ (Fin n)

def embed (n : ℕ) : R n →L[ℝ] C n :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℂ)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (fun i => Complex.ofRealCLM ∘L EuclideanSpace.proj i)

@[simp] lemma embed_apply (n : ℕ) (u : R n) (i : Fin n) : embed n u i = (u i : ℂ) := rfl

def unit (m n : ℕ) (i : Fin m) (j : Fin n) : C n →L[ℂ] C m :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin m => ℂ)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.single ℂ (fun _ : Fin m => ℂ) i ∘L EuclideanSpace.proj j

@[simp] lemma unit_apply (m n : ℕ) (i : Fin m) (j : Fin n) (u : C n) (k : Fin m) :
    unit m n i j u k = if k=i then u j else 0 := by simp [unit]

variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℝ D]
  [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D]

def multiply {m n : ℕ} (a : Fin m → Fin n → 𝓢(D,ℂ)) :
    𝓢'(D,C n) →L[ℂ] 𝓢'(D,C m) :=
  ∑ i, ∑ j, smulLeftCLM (C m) (a i j) ∘L fiberMap (unit m n i j)

lemma fiberMap_schwartz {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace E] [CompleteSpace F]
    (L : E →L[ℂ] F) (u : 𝓢(D,E)) :
    fiberMap L (u : 𝓢'(D,E)) = (SchwartzMap.postcompCLM L u : 𝓢'(D,F)) := by
  ext φ
  change L ((u : 𝓢'(D,E)) φ) = (SchwartzMap.postcompCLM L u : 𝓢'(D,F)) φ
  rw [SchwartzMap.coe_apply,SchwartzMap.coe_apply]
  have hi : Integrable (fun x => φ x • u x) := by
    simpa only [SchwartzMap.smulLeftCLM_apply φ.hasTemperateGrowth] using
      (SchwartzMap.smulLeftCLM E φ u).integrable
  rw [← L.integral_comp_comm hi]
  apply integral_congr_ae
  filter_upwards [] with x
  exact L.map_smul (φ x) (u x)

lemma product_schwartz {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (a : 𝓢(D,ℂ)) (u : 𝓢(D,F)) :
    smulLeftCLM F a (u : 𝓢'(D,F)) = (SchwartzMap.smulLeftCLM F a u : 𝓢'(D,F)) := by
  ext φ
  simp only [smulLeftCLM_apply_apply,SchwartzMap.coe_apply]
  apply integral_congr_ae
  filter_upwards [] with x
  simp [a.hasTemperateGrowth,smul_smul,mul_comm]

lemma multiply_schwartz {m n : ℕ} (a : Fin m → Fin n → 𝓢(D,ℂ)) (u : 𝓢(D,C n)) :
    multiply a (u : 𝓢'(D,C n)) =
      ((∑ i, ∑ j, SchwartzMap.smulLeftCLM (C m) (a i j)
        (SchwartzMap.postcompCLM (unit m n i j) u) : 𝓢(D,C m)) : 𝓢'(D,C m)) := by
  simp only [multiply,_root_.sum_apply,ContinuousLinearMap.comp_apply,
    fiberMap_schwartz,product_schwartz,map_sum]

end TamingCompatibility.ComplexMatrix

end

end OAI
