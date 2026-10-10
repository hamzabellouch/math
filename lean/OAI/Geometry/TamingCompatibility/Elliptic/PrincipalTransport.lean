import Mathlib
import OAI.Geometry.TamingCompatibility.Elliptic.FrozenCoefficient
import OAI.Geometry.TamingCompatibility.Charts.LinearTransport
import OAI.Geometry.TamingCompatibility.Elliptic.DirectionalPrincipal
import OAI.Geometry.TamingCompatibility.Charts.AffineBase

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.HilbertSobolev
open EuclideanSobolevOperators TemperedDistribution MeasureTheory LineDeriv
open scoped SchwartzMap LineDeriv RealInnerProductSpace
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {ι κ τ : Type*} [Fintype ι] [Fintype κ] [Fintype τ]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma directionalPrincipal_linear (L : E ≃L[ℝ] E) (v : ι → E)
    (g : ι → ι → 𝓢(E,ℂ)) (u : 𝓢'(E,F)) :
    linearDistribution L (directionalPrincipal v g u) =
      directionalPrincipal (fun i => L (v i))
        (fun i j => SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm (g i j))
        (linearDistribution L u) := by
  simp only [directionalPrincipal,map_sum,linearDistribution_product,linearDistribution_derivative]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma directionalPrincipal_zoom (p : E) (r : ℝ) (hr : r ≠ 0) (v : ι → E)
    (g : ι → ι → 𝓢(E,ℂ)) (u : 𝓢'(E,F)) :
    zoomDistribution p r hr (directionalPrincipal v g u) =
      (r⁻¹*r⁻¹) • directionalPrincipal v (fun i j => affineSchwartz p r hr (g i j))
        (zoomDistribution p r hr u) := by
  simp only [directionalPrincipal,map_sum,zoomDistribution_product,zoomDistribution_second,
    ContinuousLinearMap.map_smul_of_tower,Finset.smul_sum]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma matrixLowerOrder_linear (A : E ≃L[ℝ] E)
    (b : ι → 𝓢(E,ℂ)) (L : ι → F →L[ℂ] F) (v : ι → E)
    (c : κ → 𝓢(E,ℂ)) (K : κ → F →L[ℂ] F) (u : 𝓢'(E,F)) :
    linearDistribution A (matrixLowerOrder b L v c K u) =
      matrixLowerOrder (fun i => SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm (b i))
        L (fun i => A (v i))
        (fun i => SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm (c i)) K
        (linearDistribution A u) := by
  simp only [matrixLowerOrder,map_add,map_sum,linearDistribution_product,
    linearDistribution_postcomp,linearDistribution_derivative]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma matrixLowerOrder_zoom (p : E) (r : ℝ) (hr : r ≠ 0)
    (b : ι → 𝓢(E,ℂ)) (L : ι → F →L[ℂ] F) (v : ι → E)
    (c : κ → 𝓢(E,ℂ)) (K : κ → F →L[ℂ] F) (u : 𝓢'(E,F)) :
    zoomDistribution p r hr (matrixLowerOrder b L v c K u) =
      matrixLowerOrder (fun i => r⁻¹ • affineSchwartz p r hr (b i)) L v
        (fun i => affineSchwartz p r hr (c i)) K (zoomDistribution p r hr u) := by
  simp only [matrixLowerOrder,map_add,map_sum,zoomDistribution_product]
  simp only [zoomDistribution,affineDistribution_fiberMap,affineDistribution_derivative,
    ContinuousLinearMap.map_smul_of_tower,scalar_product_smul]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma inner_linear_basis (d : OrthonormalBasis ι ℝ E) (L : E ≃L[ℝ] E) (a x : E) :
    ⟪a,L x⟫ = ∑ i, ⟪d i,x⟫ * ⟪a,L (d i)⟫ := by
  have h := congrArg (fun y => ⟪a,L y⟫) (d.sum_repr x)
  simp only [map_sum,map_smul,inner_sum,inner_smul_right,OrthonormalBasis.repr_apply_apply] at h
  exact h.symm

lemma sum_gram_transform (a b : ι → ℝ) (c : ℝ) (u : κ → ι → ℝ) :
    (∑ i, ∑ j, (a i*b j)*(c * ∑ k,u k i*u k j)) =
      c * ∑ k,(∑ i,a i*u k i)*(∑ j,b j*u k j) := by
  simp only [Finset.mul_sum,Finset.sum_mul]
  have he (i j : ι) (k : κ) : a i*b j*(c*(u k i*u k j)) = c*(a i*u k i*(b j*u k j)) := by ring
  simp only [he]
  calc
    _ = ∑ i, ∑ k, ∑ j,c*(a i*u k i*(b j*u k j)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_comm]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma gram_covariance (d : OrthonormalBasis ι ℝ E) (L : E ≃L[ℝ] E)
    (a b : E) (c : ℝ) (u : κ → E) :
    (∑ i, ∑ j, (⟪a,L (d i)⟫ * ⟪b,L (d j)⟫) *
      (c * ∑ k,⟪d i,u k⟫ * ⟪d j,u k⟫)) = c * ∑ k,⟪a,L (u k)⟫ * ⟪b,L (u k)⟫ := by
  rw [sum_gram_transform]
  apply congrArg (fun x : ℝ => c*x)
  apply Finset.sum_congr rfl
  intro k _
  rw [inner_linear_basis d L a (u k),inner_linear_basis d L b (u k)]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring

end TamingCompatibility.HilbertSobolev

end
end

section
noncomputable section
namespace TamingCompatibility.HilbertSobolev
open EuclideanSobolevOperators TemperedDistribution MeasureTheory LineDeriv
open scoped SchwartzMap LineDeriv RealInnerProductSpace Laplacian
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma localized_coefficient_congr (χ : 𝓢(E,ℂ)) {a b : E → ℂ}
    (ha : Function.HasTemperateGrowth a) (hb : Function.HasTemperateGrowth b)
    (h : ∀ x ∈ tsupport χ, a x = b x) (u : 𝓢'(E,F)) :
    smulLeftCLM F χ (smulLeftCLM F a u) = smulLeftCLM F χ (smulLeftCLM F b u) := by
  rw [smulLeftCLM_smulLeftCLM_apply ha χ.hasTemperateGrowth,
    smulLeftCLM_smulLeftCLM_apply hb χ.hasTemperateGrowth]
  apply congrArg (fun f : E → ℂ => smulLeftCLM F f u)
  funext x
  by_cases hx : x ∈ tsupport χ
  · simp only [Pi.mul_apply,h x hx]
  · simp only [Pi.mul_apply,image_eq_zero_of_notMem_tsupport hx,mul_zero]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma local_frozen_product (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (g : 𝓢(E,ℂ)) (p : E) (r : ℝ) (hr : r ≠ 0) (c : ℂ) (hgp : g p = c)
    (ψ : 𝓢(E,ℂ)) (hψ : ∀ x ∈ tsupport ψ, χ x = 1) (u : 𝓢'(E,F)) :
    smulLeftCLM F ψ (smulLeftCLM F (frozenCoefficient χ hχ (fun x => -g x)
      (g.smooth ⊤).neg p r) u) =
      -smulLeftCLM F ψ (smulLeftCLM F (affineSchwartz p r hr g) u) +
      c • smulLeftCLM F ψ u := by
  let a := affineSchwartz p r hr g
  have ht : Function.HasTemperateGrowth (fun x => -a x+c) :=
    a.hasTemperateGrowth.neg.add (by fun_prop)
  rw [localized_coefficient_congr ψ
    (frozenCoefficient χ hχ (fun x => -g x) (g.smooth ⊤).neg p r).hasTemperateGrowth ht
    (fun x hx => by
      simp only [frozenCoefficient_apply,hψ x hx,one_mul,hgp,neg_sub_neg,
        a,affineSchwartz_apply,add_comm (r • x) p]
      ring)]
  change smulLeftCLM F ψ (smulLeftCLM F (- (a : E → ℂ) + fun _ => c) u) = _
  rw [smulLeftCLM_add a.hasTemperateGrowth.neg (by fun_prop),
    smulLeftCLM_neg a.hasTemperateGrowth]
  simp only [_root_.add_apply,_root_.neg_apply,smulLeftCLM_const,map_add,map_neg,
    map_smul]
  rfl

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in

lemma local_frozen_helmholtz (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (g : basisIndex E → basisIndex E → 𝓢(E,ℂ)) (p : E)
    (hgp : ∀ i j, g i j p = if i=j then ((((2*Real.pi)^2)⁻¹ : ℝ) : ℂ) else 0)
    (r : ℝ) (hr : r ≠ 0) (ψ : 𝓢(E,ℂ)) (hψ : ∀ x ∈ tsupport ψ, χ x = 1)
    (u : 𝓢'(E,F)) :
    smulLeftCLM F ψ (perturbedHelmholtz
      (frozenPrincipal χ hχ (fun i j x => -g i j x) (fun i j => (g i j).smooth ⊤ |>.neg) p r) u) =
      smulLeftCLM F ψ u - smulLeftCLM F ψ
        (directionalPrincipal (stdOrthonormalBasis ℝ E) (fun i j => affineSchwartz p r hr (g i j)) u) := by
  simp only [perturbedHelmholtz,differentialPerturbation,EuclideanGreen.helmholtz,
    map_add,map_sub,map_sum,frozenPrincipal]
  simp only [local_frozen_product χ hχ (g _ _) p r hr _ (hgp _ _) ψ hψ,
    Finset.sum_add_distrib,Finset.sum_neg_distrib]
  have hd : (∑ i, ∑ j, (if i=j then ((((2*Real.pi)^2)⁻¹ : ℝ) : ℂ) else 0) •
      smulLeftCLM F ψ (∂_{stdOrthonormalBasis ℝ E i} (∂_{stdOrthonormalBasis ℝ E j} u))) =
      smulLeftCLM F ψ (((2*Real.pi)^2)⁻¹ • Δ u) := by
    simp only [ite_smul,zero_smul,Finset.sum_ite_eq,Finset.mem_univ,ite_true,
      laplacian_eq_sum (stdOrthonormalBasis ℝ E),ContinuousLinearMap.map_smul_of_tower,map_sum,
      Finset.smul_sum,RCLike.real_smul_eq_coe_smul (K := ℂ),RCLike.ofReal_eq_complex_ofReal,Complex.ofReal_inv]
  rw [hd]
  simp only [directionalPrincipal,map_sum]
  abel

end TamingCompatibility.HilbertSobolev

end
end

end
end
end

end OAI
