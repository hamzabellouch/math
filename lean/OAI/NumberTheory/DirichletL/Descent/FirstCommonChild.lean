import OAI.NumberTheory.DirichletL.Descent.FirstCommonColumns

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels FirstCauchyArithmetic RayFourExpansion
open SecondPassArithmetic FourierBridge
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

include hp in
theorem firstCommonColumn_eq_rayIdealRow
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F D : Finset ι) (C : Finset ι → ℂ) (negative : Bool) (χ : RayCharacter)
    (ω : ℝ → ℂ) (X t : ℝ) (hX : 0 < X) (h : Eis) :
    firstCommonColumn p hg F D C negative χ ω X t h =
    (if negative then star (supportRay p χ D) else supportRay p χ D) *
    rayIdealRow p hg F
      (fun S => C S * if negative then
        star (ω (Real.exp (columnLog p (primeProductNorm p D*X) S)) *
          logPhase t (columnLog p (primeProductNorm p D*X) S)) else
        ω (Real.exp (columnLog p (primeProductNorm p D*X) S)) *
          logPhase t (columnLog p (primeProductNorm p D*X) S)) negative χ D h := by
  rw [rayIdealRow_eq_supportRow p hinj hg F D
    (fun S => C S * if negative then
      star (ω (Real.exp (columnLog p (primeProductNorm p D*X) S)) *
        logPhase t (columnLog p (primeProductNorm p D*X) S)) else
      ω (Real.exp (columnLog p (primeProductNorm p D*X) S)) *
        logPhase t (columnLog p (primeProductNorm p D*X) S)) negative χ h]
  simp only [firstCommonColumn,supportConjugateSum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U hU
  have hdU : Disjoint D U := Finset.disjoint_of_subset_right
    (Finset.mem_powerset.mp hU) disjoint_sdiff_self_right
  have hy : columnLog p (primeProductNorm p D*X) (D∪U) =
      Real.log (primeProductNorm p U/X) := by
    unfold columnLog
    rw [primeProductNorm_union p D U hdU,mul_div_mul_left _ _ (primeProductNorm_pos p hp D).ne']
  have hR : supportRay p χ (D∪U) = supportRay p χ D*supportRay p χ U := by
    rw [supportRay,Finset.prod_union hdU,rayCharacter_mul]
    rfl
  rw [hy,Real.exp_log (div_pos (primeProductNorm_pos p hp U) hX),hR]
  cases negative <;> simp only [Bool.false_eq_true,ite_false,ite_true,star_mul] <;> ring

variable (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))

def firstBareCubeCoefficient (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (C : Finset ι → ℂ) (d : Eis) : Finset ι → ℂ :=
  if negative then cubeMinusCoefficient p hp hcop hg B v ε₁ ε₂ C d
  else cubePlusCoefficient p hp hcop hg B v ε₁ ε₂ C d

theorem firstBareCubeCoefficient_window (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (C : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (t : ℝ) (d : Eis) :
    (fun S => firstBareCubeCoefficient p hp hg hcop B v ε₁ ε₂ negative C d S *
      if negative then star (V (y S)*logPhase t (y S)) else V (y S)*logPhase t (y S)) =
    cubeLogCoefficient p hp hcop hg B v ε₁ ε₂ negative C V y (-t) d := by
  funext S
  have ht : logPhase (-t) (-(y S)) = logPhase t (y S) := by
    unfold logPhase
    congr 1
    push_cast
    ring
  cases negative <;>
    simp only [firstBareCubeCoefficient,cubeLogCoefficient,cubeMinusCoefficient,cubePlusCoefficient,
      firstPassColumnMinus,firstPassColumnPlus,logTwistMinus,logTwistPlus,
      Bool.false_eq_true,ite_false,ite_true,ht] <;> ring

theorem firstCommonColumn_original_labels
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ j ∈ B,0 < v j)
    (negative : Bool) (χ : RayCharacter) (C : Finset ι → ℂ)
    (ω : ℝ → ℂ) (X t : ℝ) (hX : 0 < X) (c d f h : Eis) :
    firstCommonColumn p hg F D
      (firstBareCubeCoefficient p hp hg hcop B v ε₁ ε₂ negative
        (originalLabelColumn p hg B ε₁ ε₂ negative C c f) d) negative χ ω X t h =
    (if negative then star (supportRay p χ D) else supportRay p χ D) *
      (beforeDilationLabel (fun i => Ideal.span {p i}) hg p B v ε₁ ε₂ negative c d f D *
        dilatedCoreRow p hp hcop hg F D B v ε₁ ε₂ negative χ C
          (fun u => ω (Real.exp u)) (columnLog p (primeProductNorm p D*X)) c d (-t)
          (h*f^2*dilationLabel p B v ε₁ ε₂)) := by
  rw [firstCommonColumn_eq_rayIdealRow p hp hg hinj F D _ negative χ ω X t hX h,
    firstBareCubeCoefficient_window p hp hg hcop B v ε₁ ε₂ negative
      (originalLabelColumn p hg B ε₁ ε₂ negative C c f)
      (fun u => ω (Real.exp u)) (columnLog p (primeProductNorm p D*X)) t d,
    rayIdealRow_cube_labels p hp hinj hcop hg F D B v ε₁ ε₂ hv]
  rfl

theorem firstCommonColumn_marked_priority {σ : Type*} [DecidableEq σ]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (F D B A : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ j ∈ B,0 < v j)
    (negative : Bool) (χ : RayCharacter) (Ψ : Eis →* ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ) (H : Finset ι → ℂ)
    (ω : ℝ → ℂ) (X t : ℝ) (hX : 0 < X) (c d f h : Eis) :
    firstCommonColumn p hg F D
      (firstBareCubeCoefficient p hp hg hcop B v ε₁ ε₂ negative
        (originalLabelColumn p hg B ε₁ ε₂ negative
          (multiplicativeCoreColumn p Ψ m (fun U => primeMark slots lists a (A∪U)*H U)) c f) d)
      negative χ ω X t h =
    (if negative then star (supportRay p χ D) else supportRay p χ D) *
      (beforeDilationLabel (fun i => Ideal.span {p i}) hg p B v ε₁ ε₂ negative c d f D *
        ∑ r : FirstCoreIndex,firstCoreOuter p hg B v ε₁ ε₂ negative Ψ m D r *
          ∑ J ∈ slots.powerset,primeMark J lists a (A∪D) *
            firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m
              (fun U => primeMark (slots\J) (fun i => lists i\(A∪D)) a U*H U)
              (fun u => ω (Real.exp u)) (columnLog p (primeProductNorm p D*X)) c d r (-t)
              (h*f^2*dilationLabel p B v ε₁ ε₂)) := by
  rw [firstCommonColumn_original_labels p hp hg hcop hinj F D B v ε₁ ε₂ hv
    negative χ (multiplicativeCoreColumn p Ψ m (fun U => primeMark slots lists a (A∪U)*H U))
    ω X t hX c d f h]
  rw [marked_dilatedCoreRow_eq_input_family p hp hcop hg hc hpr F D B A v ε₁ ε₂
    negative χ Ψ m slots lists a H (fun u => ω (Real.exp u))
    (columnLog p (primeProductNorm p D*X)) c d (-t)]
  simp_rw [firstCoreInputRow_marked_priority]

end
end SevenEighths.InverseMoment

end OAI
