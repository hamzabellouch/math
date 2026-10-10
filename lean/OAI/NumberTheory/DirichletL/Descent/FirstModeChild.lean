import OAI.NumberTheory.DirichletL.Descent.FirstModeColumns
import OAI.NumberTheory.DirichletL.Descent.FirstPass

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic FourierBridge RayFourExpansion
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def firstModeCubeCoefficient (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (C : Finset ι → ℂ) (y : Finset ι → ℝ) (t : ℝ) (d : Eis) :
    Finset ι → ℂ :=
  if negative then cubeMinusCoefficient p hp hcop hg B v ε₁ ε₂
    (firstColumnMode true C y t) d
  else cubePlusCoefficient p hp hcop hg B v ε₁ ε₂
    (firstColumnMode false C y t) d

theorem firstModeCubeCoefficient_eq (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (C : Finset ι → ℂ) (y : Finset ι → ℝ) (t : ℝ) (d : Eis) :
    firstModeCubeCoefficient p hp hcop hg B v ε₁ ε₂ negative C y t d =
      cubeLogCoefficient p hp hcop hg B v ε₁ ε₂ negative C (fun _ => 1) y (-t) d := by
  have ht (u : ℝ) : logPhase (-t) (-u) = logPhase t u := by
    unfold logPhase
    congr 1
    push_cast
    ring
  have hm : firstColumnMode true C y t = logTwistMinus C (fun _ => 1) y (-t) := by
    funext S
    simp only [firstColumnMode,logTwistMinus,ite_true,one_mul,ht]
  have hp' : firstColumnMode false C y t = logTwistPlus C (fun _ => 1) y (-t) := by
    funext S
    simp only [firstColumnMode,logTwistPlus,Bool.false_eq_true,ite_false,one_mul,ht]
  cases negative <;>
    simp only [firstModeCubeCoefficient,cubeLogCoefficient,Bool.false_eq_true,ite_false,ite_true,hm,hp']

omit [DecidableEq σ] in
theorem actual_first_mode_marked_input
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (F D B A : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ j ∈ B, 0 < v j) (negative : Bool) (χ : RayCharacter)
    (Ψ : Eis →* ℂ) (m : Eis) (slots : Finset σ)
    (lists : σ → Finset ι) (a : σ → ι → ℂ) (H : Finset ι → ℂ)
    (y : Finset ι → ℝ) (t : ℝ) (c d f h : Eis) :
    rayIdealRow p hg F
      (firstModeCubeCoefficient p hp hcop hg B v ε₁ ε₂ negative
        (originalLabelColumn p hg B ε₁ ε₂ negative
          (multiplicativeCoreColumn p Ψ m (fun U => primeMark slots lists a (A ∪ U)*H U)) c f)
        y t d) negative χ D h =
    beforeDilationLabel (fun i => Ideal.span {p i}) hg p B v ε₁ ε₂ negative c d f D *
      ∑ r : FirstCoreIndex, firstCoreOuter p hg B v ε₁ ε₂ negative Ψ m D r *
        firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m
          (fun U => primeMark slots lists a (A ∪ U)*H U) (fun _ => 1) y c d r (-t)
          (h*f^2*dilationLabel p B v ε₁ ε₂) := by
  rw [firstModeCubeCoefficient_eq,
    rayIdealRow_cube_labels p hp hinj hcop hg F D B v ε₁ ε₂ hv]
  congr 1
  exact marked_dilatedCoreRow_eq_input_family p hp hcop hg hc hpr F D B A v ε₁ ε₂
    negative χ Ψ m slots lists a H (fun _ => 1) y c d (-t) _

theorem actual_first_mode_priority_input
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (F D B A : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ j ∈ B, 0 < v j) (negative : Bool) (χ : RayCharacter)
    (Ψ : Eis →* ℂ) (m : Eis) (slots : Finset σ)
    (lists : σ → Finset ι) (a : σ → ι → ℂ) (H : Finset ι → ℂ)
    (y : Finset ι → ℝ) (t : ℝ) (c d f h : Eis) :
    rayIdealRow p hg F
      (firstModeCubeCoefficient p hp hcop hg B v ε₁ ε₂ negative
        (originalLabelColumn p hg B ε₁ ε₂ negative
          (multiplicativeCoreColumn p Ψ m (fun U => primeMark slots lists a (A ∪ U)*H U)) c f)
        y t d) negative χ D h =
    beforeDilationLabel (fun i => Ideal.span {p i}) hg p B v ε₁ ε₂ negative c d f D *
      ∑ r : FirstCoreIndex, firstCoreOuter p hg B v ε₁ ε₂ negative Ψ m D r *
        ∑ J ∈ slots.powerset, primeMark J lists a (A ∪ D) *
          firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m
            (fun U => primeMark (slots \ J) (fun i => lists i \ (A ∪ D)) a U*H U)
            (fun _ => 1) y c d r (-t) (h*f^2*dilationLabel p B v ε₁ ε₂) := by
  rw [actual_first_mode_marked_input p hp hcop hg hinj hc hpr F D B A v ε₁ ε₂ hv]
  simp_rw [firstCoreInputRow_marked_priority]

end
end SevenEighths.InverseMoment

end OAI
