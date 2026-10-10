import OAI.NumberTheory.DirichletL.Descent.FirstProfileIdentity
import OAI.NumberTheory.DirichletL.Descent.ProfileIntegral

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels FourierBridge JointLogSeparation
open MeasureTheory
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def firstCoordinates (a : Fin 7 → ℝ) (x y : ℝ) : Fin 9 → ℝ :=
  ![a 0,a 1,a 2,a 3,a 4,a 5,a 6,x,y]

def firstOuterPhase (h : Fin 9 → ℝ) (a : Fin 7 → ℝ) : ℂ :=
  ∏ i : Fin 7, logPhase (h ⟨i.val, by omega⟩) (a i)

theorem first_mode_split (a : Fin 7 → ℝ) (x y : ℝ)
    (v : Frequency × (Fin 9 → ℝ)) :
    pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope (firstCoordinates a x y) v.1 v.2 =
      firstOuterPhase (profileHeight firstLeftSlope firstRightSlope firstKernelSlope v.1 v.2) a *
      logPhase (profileHeight firstLeftSlope firstRightSlope firstKernelSlope v.1 v.2 7) x *
      logPhase (profileHeight firstLeftSlope firstRightSlope firstKernelSlope v.1 v.2 8) y := by
  rw [pureProfileMode_height]
  simp [Fin.prod_univ_succ,firstCoordinates,firstOuterPhase]
  ring

def firstColumnMode (negative : Bool) {ι : Type*} (C : Finset ι → ℂ)
    (y : Finset ι → ℝ) (t : ℝ) (S : Finset ι) : ℂ :=
  C S * if negative then star (logPhase t (y S)) else logPhase t (y S)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem threeGaussRowFactor_first_mode (N P B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ)
    (y₁ y₂ : Finset ι → ℝ) (t₁ t₂ : ℝ) (d h : Eis) :
    threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂
      (firstColumnMode true C₁ y₁ t₁) (firstColumnMode false C₂ y₂ t₂) d h =
    logPhase t₁ (y₁ N) * logPhase t₂ (y₂ P) *
      threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h := by
  simp only [threeGaussRowFactor,firstColumnMode,Bool.false_eq_true,ite_false,ite_true,
    star_mul,star_star]
  ring

theorem actual_first_mode_ideal_rows
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (F B : Finset ι) (hFB : Disjoint F B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ)
    (d h : Eis) (a : Fin 7 → ℝ) (y₁ y₂ : Finset ι → ℝ)
    (z : Frequency × (Fin 9 → ℝ)) :
    (∑ N ∈ F.powerset, ∑ P ∈ F.powerset, if Disjoint N P then
      threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h *
        pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope
          (firstCoordinates a (y₁ N) (y₂ P)) z.1 z.2 else 0) =
    firstOuterPhase (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2) a *
      cubeBaseFactor p hp hg B v ε₁ ε₂ d h *
      idealPairReindex p hg F
        (cubeMinusCoefficient p hp hcop hg B v ε₁ ε₂
          (firstColumnMode true C₁ y₁ (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7)) d)
        (cubePlusCoefficient p hp hcop hg B v ε₁ ε₂
          (firstColumnMode false C₂ y₂ (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8)) d) h := by
  rw [mul_assoc, ← sum_threeGaussRowFactor_eq_ideal_rows p hp hinj hcop hg hc hpr F B hFB]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro P hP
  by_cases hd : Disjoint N P
  · simp only [hd,ite_true]
    rw [first_mode_split,threeGaussRowFactor_first_mode]
    ring
  · simp [hd]

end
end SevenEighths.InverseMoment

end OAI
