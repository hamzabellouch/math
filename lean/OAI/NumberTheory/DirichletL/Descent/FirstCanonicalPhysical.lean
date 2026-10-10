import OAI.NumberTheory.DirichletL.Descent.FirstMarkedColumns
import OAI.NumberTheory.DirichletL.Descent.FirstPhysicalCommon

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem canonical_residual_mul_test (b : CubeCoordinates ι) (C : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m f : O) (H test : Finset ι→ℂ) (N : Finset ι) :
    canonicalCubeResidual p hg b C negative Ψ m f (fun U=>H U*test U) N =
      canonicalCubeResidual p hg b C negative Ψ m f H N *
        test (((if negative then b.rightDivisor else b.leftDivisor)∪C)∪N) := by
  simp only [canonicalCubeResidual,originalLabelColumn,multiplicativeCoreColumn]
  ring

theorem actual_first_kernel_window_transport
    (F B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (C₁ C₂ A₁ A₂ : Finset ι→ℂ) (V₁ V₂ : ℝ→ℂ)
    (hC₁ : ∀ N∈F.powerset,C₁ N=A₁ N*star (V₁ (columnLog p 1 N)))
    (hC₂ : ∀ N∈F.powerset,C₂ N=A₂ N*V₂ (columnLog p 1 N))
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (d h : O) :
    actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W (fun _=>1) (fun _=>1) 1 1 K d h =
    ∑ N∈F.powerset,∑ Q∈F.powerset,if Disjoint N Q then
      canonicalPairMode p hp hcop hg N Q B v ε₁ ε₂ A₁ A₂ W V₁ V₂ 1 1 K d h else 0 := by
  unfold actualFirstKernel
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro Q hQ
  by_cases hd : Disjoint N Q
  · simp only [hd,ite_true,canonicalPairMode,threeGaussRowFactor,hC₁ N hN,hC₂ Q hQ,star_mul,star_star]
    ring
  · simp only [hd,ite_false]

theorem canonical_first_kernel_physical
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool : Finset ι) (b : CubeCoordinates ι) (hb : b.Admissible)
    (C : Finset ι) (hC : Disjoint C b.support)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ f : O) (H₁ H₂ : Finset ι→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (d h : O) :
    let F := pool\(b.support∪C)
    let A₁ := ‖eisEmbedding (aLabel p b.support b.rightBit)‖^2
    let A₂ := ‖eisEmbedding (aLabel p b.support b.leftBit)‖^2
    let B₁ := canonicalCubeResidual p hg b C true Ψ₁ m₁ f H₁
    let B₂ := canonicalCubeResidual p hg b C false Ψ₂ m₂ f H₂
    (‖eisEmbedding d‖^2:ℂ)⁻¹ * actualFirstKernel p hp hcop hg F b.support
      (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
      (canonicalCubeResidual p hg b C true Ψ₁ m₁ f (fun U=>H₁ U*W₁ (primeProductNorm p U)))
      (canonicalCubeResidual p hg b C false Ψ₂ m₂ f (fun U=>H₂ U*W₂ (primeProductNorm p U)))
      Φ (fun _=>1) (fun _=>1) 1 1 K d h =
    (K:ℂ)*cubeBaseFactor p hp hg b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit d h *
      firstPhysicalCommonRows p hg F
        (cubeMinusCoefficient p hp hcop hg b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit B₁ d)
        (cubePlusCoefficient p hp hcop hg b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit B₂ d)
        (fun x=>star (W₁ x)) W₂ Φ A₁ A₂ (primeProductNorm p C)
        (primeProductNorm p (cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)) K d h := by
  intro F A₁ A₂ B₁ B₂
  have hdis : Disjoint F (b.support∪C) := by
    apply Finset.disjoint_left.mpr
    intro i hi hi2
    exact (Finset.mem_sdiff.mp hi).2 hi2
  have hwindow (negative : Bool) (Ψ : O→*ℂ) (m : O) (H : Finset ι→ℂ) (W : ℝ→ℂ)
      (N : Finset ι) (hN : N∈F.powerset) :
      canonicalCubeResidual p hg b C negative Ψ m f (fun U=>H U*W (primeProductNorm p U)) N =
      canonicalCubeResidual p hg b C negative Ψ m f H N *
        W (‖eisEmbedding (aLabel p b.support (if negative then b.rightBit else b.leftBit))‖^2 *
          primeProductNorm p C*Real.exp (columnLog p 1 N)) := by
    rw [canonical_residual_mul_test p hg, cube_whole_column_norm p b hb C N hC
      (hdis.mono_left (Finset.mem_powerset.mp hN)) negative]
    simp only [columnLog,div_one,Real.exp_log (primeProductNorm_pos p hp N)]
  rw [actual_first_kernel_window_transport p hp hcop hg F b.support
    (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit _ _ B₁ B₂
    (fun y=>star (W₁ (A₁*primeProductNorm p C*Real.exp y)))
    (fun y=>W₂ (A₂*primeProductNorm p C*Real.exp y))
    (fun N hN=>by simpa only [star_star,ite_true,A₁,B₁] using hwindow true Ψ₁ m₁ H₁ W₁ N hN)
    (fun N hN=>by simpa only [Bool.false_eq_true,ite_false,A₂,B₂] using hwindow false Ψ₂ m₂ H₂ W₂ N hN)]
  exact actual_first_physical_common p hp hcop hg hinj hc hpr F b.support
    (hdis.mono_right Finset.subset_union_left) _ _ _ B₁ B₂
    (fun x=>star (W₁ x)) W₂ Φ A₁ A₂ (primeProductNorm p C) K d h

end
end SevenEighths.InverseMoment

end OAI
