import OAI.NumberTheory.DirichletL.Descent.FirstCanonicalPhysical
import OAI.NumberTheory.DirichletL.Descent.FirstPhysicalCutoff

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

def firstCubePhysicalMode (pool : Finset ι) (b : CubeCoordinates ι) (C : Finset ι)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ f : O) (H₁ H₂ : Finset ι→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (d h : O) : ℂ :=
  (K:ℂ)*cubeBaseFactor p hp hg b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit d h *
    firstPhysicalCommonRows p hg (pool\(b.support∪C))
      (cubeMinusCoefficient p hp hcop hg b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
        (canonicalCubeResidual p hg b C true Ψ₁ m₁ f H₁) d)
      (cubePlusCoefficient p hp hcop hg b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
        (canonicalCubeResidual p hg b C false Ψ₂ m₂ f H₂) d)
      (fun x=>star (W₁ x)) W₂ Φ
      (‖eisEmbedding (aLabel p b.support b.rightBit)‖^2)
      (‖eisEmbedding (aLabel p b.support b.leftBit)‖^2)
      (primeProductNorm p C)
      (primeProductNorm p (cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)) K d h

theorem canonical_retained_physical
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool : Finset ι) (b : CubeCoordinates ι) (hb : b.Admissible)
    (C : Finset ι) (hC : Disjoint C b.support)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ f : O) (H₁ H₂ : Finset ι→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (T : Finset ι→Finset O) :
    canonicalCubeDualFinite p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ f
      (fun U=>H₁ U*W₁ (primeProductNorm p U)) (fun U=>H₂ U*W₂ (primeProductNorm p U)) Φ K T =
    canonicalCubeOuter p hp hcop hg b C Ψ₁ Ψ₂ m₁ m₂ f *
      ∑ D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset,
        (UniqueFactorizationMonoid.moebius (∏i∈D,Ideal.span {p i}):ℂ)*
        ∑ h∈(T D).erase 0,firstCubePhysicalMode p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂
          W₁ W₂ Φ K (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) h := by
  unfold canonicalCubeDualFinite
  apply congrArg
  apply Finset.sum_congr rfl
  intro D hD
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  have he := canonical_first_kernel_physical p hp hcop hg hinj hc hpr pool b hb C hC
    Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W₁ W₂ Φ K (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) h
  change (‖eisEmbedding (primeSubsetGenerator (fun i=>Ideal.span {p i}) D)‖^2:ℂ)⁻¹ * _ =
    firstCubePhysicalMode p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W₁ W₂ Φ K _ h at he
  rw [←Complex.ofReal_pow,primeSubsetGenerator_norm_eq_productNorm] at he
  rw [div_eq_mul_inv,mul_assoc,he]

theorem canonical_first_physical_split
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool : Finset ι) (b : CubeCoordinates ι) (hb : b.Admissible)
    (C : Finset ι) (hC : Disjoint C b.support)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ : O) (f : Ideal O) (hf : f≠0) (H₁ H₂ : Finset ι→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) (R : Finset ι→ℝ)
    (hR : ∀ D,0≤R D) :
    let fgen := ConcretePrimeRowBridge.idealGenerator f
    let H₁' := fun U=>H₁ U*W₁ (primeProductNorm p U)
    let H₂' := fun U=>H₂ U*W₂ (primeProductNorm p U)
    let T := fun D=>childFrequencyBall
      (firstPhysicalMultiplier p b.support b.leftExponent b.rightExponent b.leftBit b.rightBit f) (R D)
    canonicalCubeBeforePoisson p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ fgen H₁' H₂' Φ K =
      canonicalCubeDualZero p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ fgen H₁' H₂' Φ K +
      (canonicalCubeOuter p hp hcop hg b C Ψ₁ Ψ₂ m₁ m₂ fgen *
        ∑ D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset,
          (UniqueFactorizationMonoid.moebius (∏i∈D,Ideal.span {p i}):ℂ)*
          ∑ h∈(T D).erase 0,firstCubePhysicalMode p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ fgen H₁ H₂
            W₁ W₂ Φ K (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) h) +
      canonicalCubeDualTail p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ fgen H₁' H₂' Φ K T := by
  intro fgen H₁' H₂' T
  rw [canonicalCubeBeforePoisson_split p hp hcop hg hinj hc pool b C Ψ₁ Ψ₂ m₁ m₂ fgen H₁' H₂' Φ K hK T]
  · rw [canonical_retained_physical p hp hcop hg hinj hc hpr pool b hb C hC]
  · intro D hD
    apply (mem_childFrequencyBall _ (firstPhysicalMultiplier_ne_zero p hp _ _ _ _ _ f hf) _ _).mpr
    simpa only [mul_zero,map_zero,norm_zero,zero_pow (by decide : 2≠0)] using hR D

end
end SevenEighths.InverseMoment

end OAI
