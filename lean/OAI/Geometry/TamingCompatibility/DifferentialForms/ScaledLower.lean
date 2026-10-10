import Mathlib
import OAI.Geometry.TamingCompatibility.Elliptic.PrincipalTransport

namespace OAI


noncomputable section
namespace TamingCompatibility.HilbertSobolev
open EuclideanSobolevOperators TemperedDistribution MeasureTheory LineDeriv
open scoped SchwartzMap LineDeriv
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma matrixLowerOrder_scale (r : ℝ)
    (b : ι → 𝓢(E,ℂ)) (L : ι → F →L[ℂ] F) (v : ι → E)
    (c : κ → 𝓢(E,ℂ)) (K : κ → F →L[ℂ] F) (u : 𝓢'(E,F)) :
    r • matrixLowerOrder b L v c K u =
      matrixLowerOrder (fun i => r • b i) L v (fun i => r • c i) K u := by
  simp only [matrixLowerOrder,smul_add,Finset.smul_sum,scalar_product_smul]

lemma matrixLowerOrder_sub_cutoff
    (b : ι → 𝓢(E,ℂ)) (L : ι → F →L[ℂ] F) (v : ι → E)
    (c : κ → 𝓢(E,ℂ)) (K : κ → F →L[ℂ] F) (χ : 𝓢(E,ℂ)) (u : 𝓢'(E,F)) :
    matrixLowerOrder b L v (Sum.elim c (fun _ : Unit => -χ))
      (Sum.elim K (fun _ : Unit => ContinuousLinearMap.id ℂ F)) u =
      matrixLowerOrder b L v c K u - smulLeftCLM F χ u := by
  simp only [matrixLowerOrder,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,
    Fintype.sum_unique]
  have he : fiberMap (ContinuousLinearMap.id ℂ F) u = u := rfl
  rw [he]
  change _ + (_ + smulLeftCLM F (- (χ : E → ℂ)) u) = _
  rw [smulLeftCLM_neg χ.hasTemperateGrowth]
  simp only [_root_.neg_apply]
  abel

lemma zoomDistribution_inverse (p : E) (r : ℝ) (hr : r ≠ 0) (u : 𝓢'(E,F)) :
    affineDistribution p r hr (zoomDistribution p r hr u) = u := by
  have h := affineDistribution_inverse (-(r⁻¹ • p)) r⁻¹ (inv_ne_zero hr) u
  simpa only [zoomDistribution,inv_inv,smul_neg,smul_smul,mul_inv_cancel₀ hr,one_smul,neg_neg] using h

lemma local_cutoff_one (χ ψ : 𝓢(E,ℂ)) (h : ∀ x ∈ tsupport ψ, χ x = 1) (u : 𝓢'(E,F)) :
    smulLeftCLM F ψ (smulLeftCLM F χ u) = smulLeftCLM F ψ u := by
  rw [localized_coefficient_congr ψ χ.hasTemperateGrowth
    (show Function.HasTemperateGrowth (fun _ : E => (1 : ℂ)) by fun_prop) h u,
    smulLeftCLM_const,one_smul]

lemma rescaled_system (p : E) (r : ℝ) (hr : r ≠ 0) (d : ι → E)
    (g : ι → ι → 𝓢(E,ℂ))
    (b : κ → 𝓢(E,ℂ)) (L : κ → F →L[ℂ] F) (v : κ → E)
    {τ : Type*} [Fintype τ] (c : τ → 𝓢(E,ℂ)) (K : τ → F →L[ℂ] F) (u : 𝓢'(E,F)) :
    (r*r) • zoomDistribution p r hr (-directionalPrincipal d g u + matrixLowerOrder b L v c K u) =
      -directionalPrincipal d (fun i j => affineSchwartz p r hr (g i j)) (zoomDistribution p r hr u) +
      matrixLowerOrder (fun i => r • affineSchwartz p r hr (b i)) L v
        (fun i => (r*r) • affineSchwartz p r hr (c i)) K (zoomDistribution p r hr u) := by
  simp only [map_add,map_neg,directionalPrincipal_zoom,matrixLowerOrder_zoom,smul_add,smul_neg,smul_smul]
  have h1 : (r*r)*(r⁻¹*r⁻¹) = 1 := by field_simp
  have h2 : r*r*r⁻¹ = r := by field_simp
  rw [h1,one_smul,matrixLowerOrder_scale]
  simp only [smul_smul,h2]

end TamingCompatibility.HilbertSobolev

end

end OAI
