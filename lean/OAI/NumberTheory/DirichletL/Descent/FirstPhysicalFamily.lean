import OAI.NumberTheory.DirichletL.Descent.FirstCanonicalEnergy
import OAI.NumberTheory.DirichletL.Descent.FirstFamilySource

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

def firstCanonicalCoefficient (b : CubeCoordinates ι) (C : Finset ι)
    (negative : Bool) (Ψ : O→*ℂ) (m d : O) (H : Finset ι→ℂ) (x : Ideal O×O) : Finset ι→ℂ :=
  firstBareCubeCoefficient p hp hg hcop b.support (fun i=>b.leftExponent i+b.rightExponent i)
    b.leftBit b.rightBit negative
    (canonicalCubeResidual p hg b C negative Ψ m (ConcretePrimeRowBridge.idealGenerator x.1) H) d

theorem firstCanonicalCoefficient_old (b : CubeCoordinates ι) (C : Finset ι)
    (negative : Bool) (Ψ : O→*ℂ) (m d : O) (H : Finset ι→ℂ) (x : Ideal O×O) :
    firstCanonicalCoefficient p hp hcop hg b C negative Ψ m d H x =
      firstOldLabelCoefficient p hp hcop hg b.support (fun i=>b.leftExponent i+b.rightExponent i)
        b.leftBit b.rightBit negative
        (multiplicativeCoreColumn p Ψ m
          (fun U=>H (((if negative then b.rightDivisor else b.leftDivisor)∪C)∪U)))
        (∏i∈C,p i) d x.1 := rfl

lemma first_unblocked_physical (F : Finset ι) (C₁ C₂ : Finset ι→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (A₁ A₂ C R K : ℝ) (d h : O) :
    firstBlockedPhysicalRows p hg F (fun _=>1) C₁ C₂ W₁ W₂ Φ A₁ A₂ C R K d h =
      firstPhysicalCommonRows p hg F C₁ C₂ W₁ W₂ Φ A₁ A₂ C R K d h := by
  rw [firstPhysicalCommonRows_indexed]
  simp only [firstBlockedPhysicalRows,one_mul]

theorem retained_first_physical_family (pool : Finset ι) (b : CubeCoordinates ι) (C : Finset ι)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ d : O) (H₁ H₂ : Finset ι→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ)
    (source : Finset (Ideal O×O)) (a : Ideal O×O→ℂ)
    (s : Fin 9→ℝ) (hs : ∀ i,0<s i) :
    (∑ x∈source,a x*canonicalCubeOuter p hp hcop hg b C Ψ₁ Ψ₂ m₁ m₂ (ConcretePrimeRowBridge.idealGenerator x.1)*
      firstCubePhysicalMode p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ (ConcretePrimeRowBridge.idealGenerator x.1)
        H₁ H₂ W₁ W₂ Φ K d x.2) =
    (K:ℂ)*firstFamilyPhysicalRows p hg source (pool\(b.support∪C)) (fun _ _=>1)
      (firstCanonicalCoefficient p hp hcop hg b C true Ψ₁ m₁ d H₁)
      (firstCanonicalCoefficient p hp hcop hg b C false Ψ₂ m₂ d H₂)
      (retainedCubeWeight p hp hcop hg b C Ψ₁ Ψ₂ m₁ m₂ d a)
      (fun x=>star (W₁ ((s 0*s 2*s 5*s 7)*x)))
      (fun x=>W₂ ((s 1*s 2*s 5*s 8)*x)) Φ
      (fun _=>‖eisEmbedding (aLabel p b.support b.rightBit)‖^2)
      (fun _=>‖eisEmbedding (aLabel p b.support b.leftBit)‖^2)
      (fun _=>primeProductNorm p C)
      (fun _=>primeProductNorm p (cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit))
      K (fun _=>d) Prod.snd s := by
  have hscale₁ : s 0*s 2*s 5*s 7≠0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (hs 0).ne' (hs 2).ne') (hs 5).ne') (hs 7).ne'
  have hscale₂ : s 1*s 2*s 5*s 8≠0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (hs 1).ne' (hs 2).ne') (hs 5).ne') (hs 8).ne'
  have hw₁ : (fun y=>star (W₁ ((s 0*s 2*s 5*s 7)*(y/(s 0*s 2*s 5*s 7))))) =
      fun y=>star (W₁ y) := by
    funext y
    rw [mul_div_cancel₀ _ hscale₁]
  have hw₂ : (fun y=>W₂ ((s 1*s 2*s 5*s 8)*(y/(s 1*s 2*s 5*s 8)))) = W₂ := by
    funext y
    rw [mul_div_cancel₀ _ hscale₂]
  simp only [firstFamilyPhysicalRows,Finset.mul_sum,hw₁,hw₂]
  apply Finset.sum_congr rfl
  intro x hx
  rw [first_unblocked_physical p hg]
  simp only [firstCubePhysicalMode,retainedCubeWeight,firstCanonicalCoefficient,
    firstBareCubeCoefficient,Bool.false_eq_true,ite_false,ite_true]
  ring

end
end SevenEighths.InverseMoment

end OAI
