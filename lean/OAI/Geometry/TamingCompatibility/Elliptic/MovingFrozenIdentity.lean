import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.ScaledLower
import OAI.Geometry.TamingCompatibility.DifferentialForms.ParameterCoefficients

namespace OAI


noncomputable section
namespace TamingCompatibility.HilbertSobolev
open MeasureTheory TemperedDistribution EuclideanSobolevOperators Filter LineDeriv Set
open scoped SchwartzMap LineDeriv Topology ContDiff ENNReal Laplacian
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma moving_local_frozen_product (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (g : 𝓢(E,ℂ)) (p₀ p : E) (r : ℝ) (hr : r ≠ 0) (c : ℂ) (hgp : g p₀ = c)
    (ψ : 𝓢(E,ℂ)) (hψ : ∀ x ∈ tsupport ψ, χ x = 1) (u : 𝓢'(E,F)) :
    smulLeftCLM F ψ (smulLeftCLM F (movingFrozenCoefficient χ hχ (fun x => -g x)
      (g.smooth ⊤).neg p₀ (r,p)) u) =
      -smulLeftCLM F ψ (smulLeftCLM F (affineSchwartz p r hr g) u) +
      c • smulLeftCLM F ψ u := by
  let a := affineSchwartz p r hr g
  have ht : Function.HasTemperateGrowth (fun x => -a x+c) :=
    a.hasTemperateGrowth.neg.add (by fun_prop)
  rw [localized_coefficient_congr ψ
    (movingFrozenCoefficient χ hχ (fun x => -g x) (g.smooth ⊤).neg p₀ (r,p)).hasTemperateGrowth ht
    (fun x hx => by
      simp only [movingFrozenCoefficient_apply,hψ x hx,one_mul,hgp,neg_sub_neg,
        a,affineSchwartz_apply,add_comm (r • x) p]
      ring)]
  change smulLeftCLM F ψ (smulLeftCLM F (- (a : E → ℂ) + fun _ => c) u) = _
  rw [smulLeftCLM_add a.hasTemperateGrowth.neg (by fun_prop),
    smulLeftCLM_neg a.hasTemperateGrowth]
  simp only [_root_.add_apply,_root_.neg_apply,smulLeftCLM_const,map_add,map_neg,
    map_smul]
  rfl

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in

lemma moving_local_frozen_helmholtz (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (g : basisIndex E → basisIndex E → 𝓢(E,ℂ)) (p₀ p : E)
    (hgp : ∀ i j, g i j p₀ = if i=j then ((((2*Real.pi)^2)⁻¹ : ℝ) : ℂ) else 0)
    (r : ℝ) (hr : r ≠ 0) (ψ : 𝓢(E,ℂ)) (hψ : ∀ x ∈ tsupport ψ, χ x = 1)
    (u : 𝓢'(E,F)) :
    smulLeftCLM F ψ (perturbedHelmholtz
      (movingFrozenPrincipal χ hχ (fun i j x => -g i j x) (fun i j => (g i j).smooth ⊤ |>.neg) p₀ (r,p)) u) =
      smulLeftCLM F ψ u - smulLeftCLM F ψ
        (directionalPrincipal (stdOrthonormalBasis ℝ E) (fun i j => affineSchwartz p r hr (g i j)) u) := by
  simp only [perturbedHelmholtz,differentialPerturbation,EuclideanGreen.helmholtz,
    map_add,map_sub,map_sum,movingFrozenPrincipal]
  simp only [moving_local_frozen_product χ hχ (g _ _) p₀ p r hr _ (hgp _ _) ψ hψ,
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

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma moving_local_frozen_system {ι κ : Type*} [Fintype ι] [Fintype κ]
    (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (g : basisIndex E → basisIndex E → 𝓢(E,ℂ)) (p₀ p : E)
    (hgp : ∀ i j, g i j p₀ = if i=j then ((((2*Real.pi)^2)⁻¹ : ℝ) : ℂ) else 0)
    (r : ℝ) (hr : r ≠ 0) (ψ : 𝓢(E,ℂ)) (hψ : ∀ x ∈ tsupport ψ, χ x = 1)
    (B : ι → 𝓢(E,ℂ)) (L : ι → F →L[ℂ] F) (v : ι → E)
    (C : κ → 𝓢(E,ℂ)) (K : κ → F →L[ℂ] F) (u : 𝓢'(E,F)) :
    smulLeftCLM F ψ (perturbedHelmholtz
      (movingFrozenPrincipal χ hχ (fun i j x => -g i j x) (fun i j => (g i j).smooth ⊤ |>.neg) p₀ (r,p)) u +
      matrixLowerOrder B L v (Sum.elim C (fun _ : Unit => -χ))
        (Sum.elim K (fun _ : Unit => ContinuousLinearMap.id ℂ F)) u) =
    smulLeftCLM F ψ (-directionalPrincipal (stdOrthonormalBasis ℝ E)
      (fun i j => affineSchwartz p r hr (g i j)) u + matrixLowerOrder B L v C K u) := by
  rw [map_add,moving_local_frozen_helmholtz χ hχ g p₀ p hgp r hr ψ hψ u,
    matrixLowerOrder_sub_cutoff B L v C K χ u,map_sub,local_cutoff_one χ ψ hψ u]
  simp only [map_add,map_neg]
  abel

end TamingCompatibility.HilbertSobolev

end

end OAI
