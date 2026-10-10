import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.PerturbationNeg

namespace OAI

noncomputable section
namespace TamingCompatibility.HilbertSobolev
open MeasureTheory TemperedDistribution EuclideanSobolevOperators
open scoped SchwartzMap ENNReal LineDeriv
section FiberMaps

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

def fiberMap (L : F →L[ℂ] G) : 𝓢'(E,F) →L[ℂ] 𝓢'(E,G) :=
  PointwiseConvergenceCLM.postcomp 𝓢(E,ℂ) L

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [CompleteSpace F] [CompleteSpace G] in
lemma fiberMap_apply (L : F →L[ℂ] G) (u : 𝓢'(E,F)) (φ : 𝓢(E,ℂ)) :
    fiberMap L u φ = L (u φ) := rfl

omit [CompleteSpace F] [CompleteSpace G] in
lemma fiberMap_bessel (L : F →L[ℂ] G) (s : ℝ) (u : 𝓢'(E,F)) :
    fiberMap L (besselPotential E F s u) = besselPotential E G s (fiberMap L u) := by
  ext φ
  rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [CompleteSpace F] [CompleteSpace G] in
lemma fiberMap_derivative (L : F →L[ℂ] G) (v : E) (u : 𝓢'(E,F)) :
    fiberMap L (∂_{v} u) = ∂_{v} (fiberMap L u) := by
  ext φ
  rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [CompleteSpace F] [CompleteSpace G] in
lemma fiberMap_product (L : F →L[ℂ] G) (g : E → ℂ) (u : 𝓢'(E,F)) :
    fiberMap L (smulLeftCLM F g u) = smulLeftCLM G g (fiberMap L u) := by
  ext φ
  rfl

lemma fiberMap_Lp (L : F →L[ℂ] G) (u : Lp F 2 (volume : Measure E)) :
    fiberMap L (u : 𝓢'(E,F)) = (L.compLp u : 𝓢'(E,G)) := by
  ext φ
  rw [fiberMap_apply, Lp.toTemperedDistribution_apply, Lp.toTemperedDistribution_apply]
  have hφ : Integrable (fun x => φ x • u x) (volume : Measure E) := by
    exact memLp_one_iff_integrable.mp ((φ.memLp 2 volume).smul (Lp.memLp u))
  rw [← L.integral_comp_comm hφ]
  apply integral_congr_ae
  filter_upwards [L.coeFn_compLp u] with x hx
  rw [hx, L.map_smul]

lemma MemSobolev_fiberMap {s : ℝ} {u : 𝓢'(E,F)} (hu : MemSobolev s 2 u)
    (L : F →L[ℂ] G) : MemSobolev s 2 (fiberMap L u) := by
  obtain ⟨v, hv⟩ := hu
  refine ⟨L.compLp v, ?_⟩
  rw [← fiberMap_bessel, hv, fiberMap_Lp]

def fiberOperator (s : ℝ) (L : F →L[ℂ] G) : H E F s →L[ℂ] H E G s :=
  L.compLpL 2 volume

lemma toDistribution_fiberOperator (s : ℝ) (L : F →L[ℂ] G) (u : H E F s) :
    toDistribution E G s (fiberOperator s L u) = fiberMap L (toDistribution E F s u) := by
  change besselPotential E G (-s) (L.compLp u : 𝓢'(E,G)) =
    fiberMap L (besselPotential E F (-s) (u : 𝓢'(E,F)))
  rw [fiberMap_bessel, fiberMap_Lp]

end FiberMaps

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def matrixLowerOrder {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : ι → 𝓢(E,ℂ)) (L : ι → F →L[ℂ] F) (v : ι → E)
    (c : κ → 𝓢(E,ℂ)) (K : κ → F →L[ℂ] F) (u : 𝓢'(E,F)) : 𝓢'(E,F) :=
  (∑ i, smulLeftCLM F (b i) (fiberMap (L i) (∂_{v i} u))) +
  ∑ k, smulLeftCLM F (c k) (fiberMap (K k) u)

lemma matrixLowerOrder_memSobolev {ι κ : Type*} [Fintype ι] [Fintype κ]
    (n : ℕ) (b : ι → 𝓢(E,ℂ)) (L : ι → F →L[ℂ] F) (v : ι → E)
    (c : κ → 𝓢(E,ℂ)) (K : κ → F →L[ℂ] F)
    {u : 𝓢'(E,F)} (hu : MemSobolev ((n:ℝ)+1) 2 u) :
    MemSobolev n 2 (matrixLowerOrder b L v c K u) := by
  apply MemSobolev.add
  · apply memSobolev_sum
    intro i _
    apply memSobolev_nat_product
    apply MemSobolev_fiberMap
    convert hu.lineDerivOp (m := v i) using 1
    ring
  · apply memSobolev_sum
    intro k _
    exact memSobolev_nat_product n (c k)
      (MemSobolev_fiberMap (hu.mono (by linarith)) (K k))

theorem matrix_cutoff_H1_regular {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : basisIndex E → basisIndex E → 𝓢(E,ℂ))
    (hweak : ‖perturbationNegOne (F := F) a‖ < 1)
    (hstrong : ‖perturbation (F := F) 0 a‖ < 1)
    (b : ι → 𝓢(E,ℂ)) (L : ι → F →L[ℂ] F) (v : ι → E)
    (c : κ → 𝓢(E,ℂ)) (K : κ → F →L[ℂ] F) (g : 𝓢(E,ℂ))
    {u : 𝓢'(E,F)} (hu : MemSobolev 1 2 u)
    (hf : MemSobolev 0 2 (smulLeftCLM F g
      (perturbedHelmholtz a u + matrixLowerOrder b L v c K u))) :
    MemSobolev 2 2 (smulLeftCLM F g u) := by
  apply cutoff_H1_regular a hweak hstrong g hu
  have hu' : MemSobolev ((0:ℕ)+1:ℝ) 2 u := by simpa using hu
  have hl : MemSobolev (0:ℕ) 2 (matrixLowerOrder b L v c K u) :=
    matrixLowerOrder_memSobolev 0 b L v c K hu'
  have hg : MemSobolev 0 2 (smulLeftCLM F g (matrixLowerOrder b L v c K u)) := by
    simpa only [Nat.cast_zero] using memSobolev_nat_product (E := E) (F := F) 0 g hl
  rw [map_add] at hf
  simpa only [add_sub_cancel_right] using hf.sub hg

end TamingCompatibility.HilbertSobolev

end

end OAI
