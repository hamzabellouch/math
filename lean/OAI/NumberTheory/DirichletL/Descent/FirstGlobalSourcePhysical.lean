import OAI.NumberTheory.DirichletL.Descent.FirstGlobalSourceSupport
import OAI.NumberTheory.DirichletL.Descent.FirstGlobalSourceIndex

namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem firstCubePhysicalMode_fixed_pool (pool : Finset ι) (b : CubeCoordinates ι) (C : Finset ι)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ d : O) (H₁ H₂ : Finset ι→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (x : Ideal O×O) :
    firstCubePhysicalMode p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂
      (ConcretePrimeRowBridge.idealGenerator x.1) H₁ H₂ W₁ W₂ Φ K d x.2=
    (K:ℂ)*cubeBaseFactor p hp hg b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit d x.2 *
      firstPhysicalCommonRows p hg pool
        (firstCanonicalCoefficient p hp hcop hg b C true Ψ₁ m₁ d H₁ x)
        (firstCanonicalCoefficient p hp hcop hg b C false Ψ₂ m₂ d H₂ x)
        (fun y=>star (W₁ y)) W₂ Φ
        (‖eisEmbedding (aLabel p b.support b.rightBit)‖^2)
        (‖eisEmbedding (aLabel p b.support b.leftBit)‖^2)
        (primeProductNorm p C)
        (primeProductNorm p (cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)) K d x.2 := by
  change _*firstPhysicalCommonRows p hg (pool\(b.support∪C))
      (firstCanonicalCoefficient p hp hcop hg b C true Ψ₁ m₁ d H₁ x)
      (firstCanonicalCoefficient p hp hcop hg b C false Ψ₂ m₂ d H₂ x) _ _ _ _ _ _ _ _ _ _ = _
  apply congrArg (fun z : ℂ =>
    (K : ℂ) * cubeBaseFactor p hp hg b.support
      (fun i => b.leftExponent i + b.rightExponent i) b.leftBit b.rightBit d x.2 * z)
  apply firstPhysicalCommonRows_fixed_pool p hg _ pool Finset.sdiff_subset
  · intro U hU hn
    apply firstCanonicalCoefficient_zero_overlap p hp hcop hg
    intro hd
    apply hn
    intro i hi
    exact Finset.mem_sdiff.mpr ⟨hU hi,fun he=>Finset.disjoint_left.mp hd hi he⟩
  · intro U hU hn
    apply firstCanonicalCoefficient_zero_overlap p hp hcop hg
    intro hd
    apply hn
    intro i hi
    exact Finset.mem_sdiff.mpr ⟨hU hi,fun he=>Finset.disjoint_left.mp hd hi he⟩

theorem original_retained_global_family
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (labels : Finset (Ideal O)) (hlabels : ∀I∈labels,I≠0)
    (β : Ideal O→(ι→₀ℕ)→ℂ) (Ψ : O→*ℂ) (m : O)
    (mark : (ι→₀ℕ)→Finset ι→ℂ) (W : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K Y : ℝ)
    (R : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (hRY : ∀k∈firstOriginalOuter pool Q,∀f∈labels,R k.1 k.2.1 f k.2.2≤Y)
    (s : Fin 9→ℝ) (hs : ∀i,0<s i) :
    reopenedPhysicalSourceSum pool Q labels β (fun b C I=>
      reopenedPhysicalRetained p hp hcop hg pool b C Ψ m I mark W Φ K (R b C I)) =
    (K:ℂ)*firstFamilyPhysicalRows p hg
      (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun k=>k.1) Y) pool
      (fun _ _=>1)
      (fun x=>firstCanonicalCoefficient p hp hcop hg x.1.1 x.1.2.1 true Ψ m
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.1.2.2) (mark x.1.1.rightExponent) x.2)
      (fun x=>firstCanonicalCoefficient p hp hcop hg x.1.1 x.1.2.1 false Ψ m
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.1.2.2) (mark x.1.1.leftExponent) x.2)
      (fun x=>retainedCubeWeight p hp hcop hg x.1.1 x.1.2.1 Ψ Ψ m m
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.1.2.2) (firstOriginalWeight p β R x.1) x.2)
      (fun y=>star (W ((s 0*s 2*s 5*s 7)*y))) (fun y=>W ((s 1*s 2*s 5*s 8)*y)) Φ
      (fun x=>‖eisEmbedding (aLabel p x.1.1.support x.1.1.rightBit)‖^2)
      (fun x=>‖eisEmbedding (aLabel p x.1.1.support x.1.1.leftBit)‖^2)
      (fun x=>primeProductNorm p x.1.2.1)
      (fun x=>primeProductNorm p (cubeActiveSupport x.1.1.support
        (fun i=>x.1.1.leftExponent i+x.1.1.rightExponent i) x.1.1.leftBit x.1.1.rightBit)) K
      (fun x=>primeSubsetGenerator (fun i=>Ideal.span {p i}) x.1.2.2) (fun x=>x.2.2) s := by
  rw [original_retained_global_index p hp hcop hg pool Q labels hlabels β Ψ m mark W Φ K Y R hRY]
  have hleft : s 0*s 2*s 5*s 7≠0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (ne_of_gt (hs 0)) (ne_of_gt (hs 2))) (ne_of_gt (hs 5))) (ne_of_gt (hs 7))
  have hright : s 1*s 2*s 5*s 8≠0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (ne_of_gt (hs 1)) (ne_of_gt (hs 2))) (ne_of_gt (hs 5))) (ne_of_gt (hs 8))
  have hw₁ : (fun y=>star (W ((s 0*s 2*s 5*s 7)*(y/(s 0*s 2*s 5*s 7)))))=fun y=>star (W y) := by
    funext y
    rw [mul_div_cancel₀ _ hleft]
  have hw₂ : (fun y=>W ((s 1*s 2*s 5*s 8)*(y/(s 1*s 2*s 5*s 8))))=W := by
    funext y
    rw [mul_div_cancel₀ _ hright]
  simp only [firstFamilyPhysicalRows,Finset.mul_sum,hw₁,hw₂]
  apply Finset.sum_congr rfl
  intro x hx
  rw [first_unblocked_physical,firstCubePhysicalMode_fixed_pool p hp hcop hg]
  unfold retainedCubeWeight
  ring

end
end SevenEighths.InverseMoment

end OAI
