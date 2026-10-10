import OAI.NumberTheory.DirichletL.Descent.SecondPass

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open FirstCauchyArithmetic RayFourExpansion
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

omit [DecidableEq σ] in
theorem marked_dilatedCoreRow_eq_input_family
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda ^ 2 ∣ p i - 1)
    (F D B A : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : Eis →* ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ)
    (c d : Eis) (t : ℝ) (z : Eis) :
    dilatedCoreRow p hp hcop hg F D B v ε₁ ε₂ negative χ
      (multiplicativeCoreColumn p Ψ m (fun U => primeMark slots lists a (A ∪ U) * H U))
      V y c d t z =
    ∑ r : FirstCoreIndex, firstCoreOuter p hg B v ε₁ ε₂ negative Ψ m D r *
      firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m
        (fun U => primeMark slots lists a (A ∪ U) * H U) V y c d r t z :=
  dilatedCoreRow_eq_input_family p hp hcop hg hc hpr F D B v ε₁ ε₂ negative χ Ψ m _ V y c d t z

theorem firstCoreInputRow_marked_priority
    (F D B A : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : Eis →* ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ)
    (c d : Eis) (r : FirstCoreIndex) (t : ℝ) (z : Eis) :
    firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m
      (fun U => primeMark slots lists a (A ∪ U) * H U) V y c d r t z =
    ∑ J ∈ slots.powerset, primeMark J lists a (A ∪ D) *
      firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m
        (fun U => primeMark (slots \ J) (fun i => lists i \ (A ∪ D)) a U * H U)
        V y c d r t z := by
  unfold firstCoreInputRow inputConjugateRow supportConjugateSum
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro U hU
  have he := primeMark_priority slots lists a (A ∪ D) U
  simp only [primeMark_residual_lists] at he
  have hset : (D ∪ U) \ (A ∪ D) = U \ (A ∪ D) := by
    ext i
    simp only [Finset.mem_sdiff, Finset.mem_union]
    tauto
  simp only [secondInputCoefficient, firstCoreTest, ← Finset.union_assoc]
  rw [he]
  simp only [Finset.sum_mul, Finset.mul_sum, ← primeMark_residual_lists, hset]
  apply Finset.sum_congr rfl
  intro J hJ
  ring

theorem firstCoreInputRow_fixed_pool
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : Eis →* ℂ) (m : Eis)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ)
    (c d : Eis) (r : FirstCoreIndex) (t : ℝ) (z : Eis) :
    firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t z =
      inputConjugateRow p hg F (firstCoreTwist negative χ Ψ r)
        ((m * b0Label p B v ε₁ ε₂) * ∏ i ∈ D, p i)
        (c * jLabel p B v ε₁ ε₂) d (firstCoreTest H V y negative t D)
        (if negative then -z else z) :=
  inputConjugateRow_fixed_pool p hg hinj F D _ _ _ _ _ _

end
end SevenEighths.InverseMoment

end OAI
