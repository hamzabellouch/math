import Mathlib
import OAI.Geometry.TamingCompatibility.Elliptic.FrozenSystem

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.HilbertSobolev
open EuclideanSobolevOperators TemperedDistribution MeasureTheory LineDeriv
open scoped SchwartzMap LineDeriv RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma principalInBasis_apply (B : OrthonormalBasis κ ℝ E) (v : ι → E)
    (g : ι → ι → 𝓢(E,ℂ)) (a b : κ) (x : E) :
    principalInBasis B v g a b x = ∑ i, ∑ j, ((⟪B a,v i⟫ * ⟪B b,v j⟫ : ℝ) : ℂ) * g i j x := by
  simp only [principalInBasis,_root_.sum_apply,_root_.smul_apply,Complex.real_smul]

lemma normalized_principal_center [DecidableEq κ]
    (d : OrthonormalBasis ι ℝ E) (B : OrthonormalBasis κ ℝ E)
    (L : E ≃L[ℝ] E) (v : ι → E) (s c k : ℝ)
    (hL : ∀ i, L (v i) = s • d i) (hc : c*(s*s) = k)
    (g : ι → ι → 𝓢(E,ℂ)) (p : E)
    (hg : ∀ i j, g i j p = (c * ∑ t,⟪d i,v t⟫ * ⟪d j,v t⟫ : ℝ)) (a b : κ) :
    principalInBasis B (fun i => L (d i))
      (fun i j => SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm (g i j)) a b (L p) =
      if a=b then (k : ℂ) else 0 := by
  rw [principalInBasis_apply]
  simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply,Function.comp_apply,
    ContinuousLinearEquiv.symm_apply_apply,hg,← Complex.ofReal_mul,← Complex.ofReal_sum]
  rw [gram_covariance]
  simp only [hL,inner_smul_right]
  have he : (∑ t,(s*⟪B a,d t⟫)*(s*⟪B b,d t⟫)) = (s*s)*⟪B a,B b⟫ := by
    rw [← d.sum_inner_mul_inner (B a) (B b),Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [real_inner_comm (d i) (B b)]
    ring
  rw [he,← mul_assoc,hc,B.inner_eq_ite]
  split_ifs <;> simp

end TamingCompatibility.HilbertSobolev

end
end

section
noncomputable section
namespace TamingCompatibility.HilbertSobolev
open EuclideanSobolevOperators TemperedDistribution MeasureTheory LineDeriv Set Filter
open scoped SchwartzMap LineDeriv Topology ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma memSobolevLoc_linear_one (L : E ≃L[ℝ] E) {U : Set E} {u : 𝓢'(E,F)}
    (hu : MemSobolevLoc U 1 u) : MemSobolevLoc (L.symm ⁻¹' U) 1 (linearDistribution L u) := by
  have hu' : MemSobolevLoc U (1 : ℕ) u := by simpa only [Nat.cast_one] using hu
  simpa only [Nat.cast_one] using memSobolevLoc_linear 1 L hu'

theorem linearly_normalized_interior_regular {ι κ τ : Type*}
    [Fintype ι] [Fintype κ] [Fintype τ]
    {U : Set E} (hU : IsOpen U) (p : E) (hp : p ∈ U)
    (d : ι → E) (g : ι → ι → 𝓢(E,ℂ)) (A : E ≃L[ℝ] E)
    (hgp : ∀ i j, principalInBasis (stdOrthonormalBasis ℝ E) (fun i => A (d i))
      (fun i j => SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm (g i j)) i j (A p) =
        if i=j then ((((2*Real.pi)^2)⁻¹ : ℝ) : ℂ) else 0)
    (b : κ → 𝓢(E,ℂ)) (L : κ → F →L[ℂ] F) (v : κ → E)
    (c : τ → 𝓢(E,ℂ)) (K : τ → F →L[ℂ] F) {u : 𝓢'(E,F)}
    (hu : MemSobolevLoc U 1 u)
    (hf : ∀ n : ℕ, MemSobolevLoc U n
      (-directionalPrincipal d g u + matrixLowerOrder b L v c K u)) :
    ∃ V : Set E, IsOpen V ∧ p ∈ V ∧ V ⊆ U ∧ ∀ n : ℕ, MemSobolevLoc V n u := by
  let G := principalInBasis (stdOrthonormalBasis ℝ E) (fun i => A (d i))
    (fun i j => SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm (g i j))
  let B := fun i => SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm (b i)
  let C := fun i => SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm (c i)
  have hf' (n : ℕ) : MemSobolevLoc (A.symm ⁻¹' U) n
      (-directionalPrincipal (stdOrthonormalBasis ℝ E) G (linearDistribution A u) +
        matrixLowerOrder B L (fun i => A (v i)) C K (linearDistribution A u)) := by
    have h := memSobolevLoc_linear n A (hf n)
    rw [map_add,map_neg,directionalPrincipal_linear,matrixLowerOrder_linear,
      directionalPrincipal_basis (stdOrthonormalBasis ℝ E)] at h
    exact h
  obtain ⟨V,hV,hpV,hVU,hall⟩ := normalized_scalar_interior_regular
    (hU.preimage A.symm.continuous) (A p) (by simpa only [mem_preimage,ContinuousLinearEquiv.symm_apply_apply] using hp)
    G hgp B L (fun i => A (v i)) C K (memSobolevLoc_linear_one A hu) hf'
  refine ⟨A ⁻¹' V,hV.preimage A.continuous,hpV,?_,fun n => ?_⟩
  · intro x hx
    have h := hVU hx
    simpa only [mem_preimage,ContinuousLinearEquiv.symm_apply_apply] using h
  · have h := memSobolevLoc_linear n A.symm (hall n)
    rw [linearDistribution_inverse] at h
    exact h

end TamingCompatibility.HilbertSobolev

end
end

end
end
end

end OAI
