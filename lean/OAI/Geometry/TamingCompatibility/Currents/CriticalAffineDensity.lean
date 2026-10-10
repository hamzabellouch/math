import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.ScaledLower
import OAI.Geometry.TamingCompatibility.DifferentialForms.CriticalRescale

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.HilbertSobolev
open MeasureTheory TemperedDistribution EuclideanSobolevOperators Set LineDeriv
open scoped SchwartzMap LineDeriv
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in

lemma affineDistribution_schwartz (p : E) (r : ℝ) (hr : r ≠ 0)
    (f : 𝓢(E,F)) :
    affineDistribution p r hr (f : 𝓢'(E,F)) =
      |(r ^ Module.finrank ℝ E)⁻¹| •
        (rescaleSchwartz (-(r⁻¹ • p)) r⁻¹ (inv_ne_zero hr) f : 𝓢'(E,F)) := by
  ext φ
  rw [affineDistribution_apply]
  simp only [SchwartzMap.toTemperedDistributionCLM_apply_apply, _root_.smul_apply,
    affineSchwartz_apply, rescaleSchwartz_apply]
  change (∫ x, φ (r • x+p) • f x) =
    |(r ^ Module.finrank ℝ E)⁻¹| • ∫ y, φ y • f (r⁻¹ • y + -(r⁻¹ • p))
  let h : E → F := fun y => φ y • f (r⁻¹ • y + -(r⁻¹ • p))
  let k : E → F := fun y => φ (y+p) • f (r⁻¹ • y)
  have he : (fun x => φ (r • x+p) • f x) = fun x => k (r • x) := by
    funext x
    simp [k, inv_smul_smul₀ hr]
  rw [he, Measure.integral_comp_smul]
  congr 1
  have ha := integral_add_right_eq_self (μ := (volume : Measure E)) h p
  refine Eq.trans ?_ ha
  apply integral_congr_ae
  filter_upwards [] with y
  simp [h,k,smul_add]

omit [CompleteSpace F] in
lemma zoomDistribution_schwartz (p : E) (r : ℝ) (hr : r ≠ 0)
    (f : 𝓢(E,F)) :
    zoomDistribution p r hr (f : 𝓢'(E,F)) =
      |r ^ Module.finrank ℝ E| • (rescaleSchwartz p r hr f : 𝓢'(E,F)) := by
  rw [zoomDistribution,affineDistribution_schwartz]
  simp only [inv_pow,inv_inv,smul_neg,smul_smul,mul_inv_cancel₀ hr,one_smul,neg_neg]

omit [CompleteSpace F] in

lemma rescaled_schwartz_system (p : E) (r : ℝ) (hr : r ≠ 0)
    {ι κ τ : Type*} [Fintype ι] [Fintype κ] [Fintype τ]
    (d : ι → E) (g : ι → ι → 𝓢(E,ℂ))
    (b : κ → 𝓢(E,ℂ)) (L : κ → F →L[ℂ] F) (v : κ → E)
    (c : τ → 𝓢(E,ℂ)) (K : τ → F →L[ℂ] F) (u f : 𝓢(E,F))
    (heq : -directionalPrincipal d g (u : 𝓢'(E,F)) +
      matrixLowerOrder b L v c K (u : 𝓢'(E,F)) = (f : 𝓢'(E,F))) :
    -directionalPrincipal d (fun i j => affineSchwartz p r hr (g i j))
        (rescaleSchwartz p r hr u : 𝓢'(E,F)) +
      matrixLowerOrder (fun i => r • affineSchwartz p r hr (b i)) L v
        (fun i => (r*r) • affineSchwartz p r hr (c i)) K
          (rescaleSchwartz p r hr u : 𝓢'(E,F)) =
      r^2 • (rescaleSchwartz p r hr f : 𝓢'(E,F)) := by
  have hs := rescaled_system p r hr d g b L v c K (u : 𝓢'(E,F))
  rw [heq,zoomDistribution_schwartz,zoomDistribution_schwartz] at hs
  have hh : |r ^ Module.finrank ℝ E| ≠ 0 := abs_ne_zero.mpr (pow_ne_zero _ hr)
  apply (smul_right_injective (M := 𝓢'(E,F)) hh)
  dsimp only [directionalPrincipal,matrixLowerOrder] at hs ⊢
  simp only [lineDerivOp_smul,ContinuousLinearMap.map_smul_of_tower,
    ← Finset.smul_sum,← smul_neg,← smul_add] at hs
  rw [smul_comm] at hs
  simpa only [pow_two] using hs.symm

end TamingCompatibility.HilbertSobolev

end
end

section
noncomputable section
namespace TamingCompatibility.HilbertSobolev
open MeasureTheory TemperedDistribution EuclideanSobolevOperators Set LineDeriv
open scoped SchwartzMap LineDeriv
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] [FiniteDimensional ℝ E] in
lemma affineSchwartz_inverse_comp (p : E) (r : ℝ) (hr : r ≠ 0) (ψ : 𝓢(E,ℂ)) :
    affineSchwartz p r hr (affineSchwartz (-(r⁻¹ • p)) r⁻¹ (inv_ne_zero hr) ψ) = ψ := by
  ext x
  simp only [affineSchwartz_apply,affine_inverse_point p x hr]

omit [CompleteSpace F] in

lemma rescaled_local_schwartz_system (p : E) (r : ℝ) (hr : r ≠ 0)
    {ι κ τ : Type*} [Fintype ι] [Fintype κ] [Fintype τ]
    (d : ι → E) (g : ι → ι → 𝓢(E,ℂ))
    (b : κ → 𝓢(E,ℂ)) (L : κ → F →L[ℂ] F) (v : κ → E)
    (c : τ → 𝓢(E,ℂ)) (K : τ → F →L[ℂ] F) (u f : 𝓢(E,F)) (ψ : 𝓢(E,ℂ))
    (heq : smulLeftCLM F (affineSchwartz (-(r⁻¹ • p)) r⁻¹ (inv_ne_zero hr) ψ)
      (-directionalPrincipal d g (u : 𝓢'(E,F)) + matrixLowerOrder b L v c K (u : 𝓢'(E,F))) =
      smulLeftCLM F (affineSchwartz (-(r⁻¹ • p)) r⁻¹ (inv_ne_zero hr) ψ) (f : 𝓢'(E,F))) :
    smulLeftCLM F ψ (-directionalPrincipal d (fun i j => affineSchwartz p r hr (g i j))
        (rescaleSchwartz p r hr u : 𝓢'(E,F)) +
      matrixLowerOrder (fun i => r • affineSchwartz p r hr (b i)) L v
        (fun i => (r*r) • affineSchwartz p r hr (c i)) K
          (rescaleSchwartz p r hr u : 𝓢'(E,F))) =
      smulLeftCLM F ψ (r^2 • (rescaleSchwartz p r hr f : 𝓢'(E,F))) := by
  have ht := congrArg (zoomDistribution p r hr) heq
  simp only [zoomDistribution_product,affineSchwartz_inverse_comp] at ht
  have hs := congrArg (smulLeftCLM F ψ) (rescaled_system p r hr d g b L v c K (u : 𝓢'(E,F)))
  rw [ContinuousLinearMap.map_smul_of_tower,ht,zoomDistribution_schwartz,zoomDistribution_schwartz] at hs
  have hh : |r ^ Module.finrank ℝ E| ≠ 0 := abs_ne_zero.mpr (pow_ne_zero _ hr)
  apply (smul_right_injective (M := 𝓢'(E,F)) hh)
  dsimp only [directionalPrincipal,matrixLowerOrder] at hs ⊢
  simp only [lineDerivOp_smul,ContinuousLinearMap.map_smul_of_tower,
    ← Finset.smul_sum,← smul_neg,← smul_add] at hs
  rw [smul_comm] at hs
  simpa only [pow_two,ContinuousLinearMap.map_smul_of_tower] using hs.symm

end TamingCompatibility.HilbertSobolev

end
end

end
end
end

end OAI
