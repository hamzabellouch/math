import OAI.NumberTheory.DirichletL.Descent.SecondModeEnergy
import OAI.NumberTheory.DirichletL.Inversion.InitialClippedColumns

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open JointLogSeparation IdealMobiusDivisorSum InverseInitialClippedColumns
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma child_ball_neg (R : ℝ) (k : Eis) :
    -k ∈ nonzeroChildFrequencyBall 1 R ↔ k ∈ nonzeroChildFrequencyBall 1 R := by
  simp only [mem_nonzeroChildFrequencyBall _ one_ne_zero,one_mul,map_neg,norm_neg]

lemma child_ball_sum_neg {β : Type*} [AddCommMonoid β] (R : ℝ) (F : Eis → β) :
    ∑ k ∈ nonzeroChildFrequencyBall 1 R,F (-k) =
      ∑ k ∈ nonzeroChildFrequencyBall 1 R,F k := by
  apply Finset.sum_bij (fun k _ => -k)
  · intro k hk
    exact (child_ball_neg R k).mpr hk
  · intro a ha b hb he
    exact neg_injective he
  · intro b hb
    exact ⟨-b,(child_ball_neg R b).mpr hb,neg_neg b⟩
  · intro k hk
    rfl

variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def secondLabelWeight (K : ℕ) (f : Ideal Eis) : ℝ := ((idealDivisors f).card : ℝ)^(9+4*K)

theorem second_left_normalized_energy
    (K : ℕ) (labels : Finset (Ideal Eis)) (rows : Finset Eis) (γ : OuterTriple)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (ω : ℝ → ℂ) (Z N V : ℝ) (hZ : 0 < Z) (t : Frequency × (Fin 6 → ℝ)) :
    secondLabelEnergy K labels rows (secondModeLeft p hp hcop hg pool Ψ m z slots lists a ω (Z^N) t) γ =
      Z^(max 0 N+V) * normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ z)
        (actualSecondInheritedPuncture m γ) slots lists a labels rows (secondLabelWeight K)
        (clippedTest ω (Z^(max 0 N-N)) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
        (Z^(max 0 N)) Z (max 0 N+V) := by
  exact initial_columnEnergy_clipping_normalized p hp hcop hg pool (secondRayMinus Ψ z)
    (actualSecondInheritedPuncture m γ) slots lists a labels rows (secondLabelWeight K) ω hZ N V _

theorem second_right_normalized_energy
    (K : ℕ) (labels : Finset (Ideal Eis)) (R : ℝ) (γ : OuterTriple)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (ω : ℝ → ℂ) (Z N V : ℝ) (hZ : 0 < Z) (t : Frequency × (Fin 6 → ℝ)) :
    secondLabelEnergy K labels (nonzeroChildFrequencyBall 1 R)
      (secondModeRight p hp hcop hg pool Ψ m z slots lists a ω (Z^N) t) γ =
      Z^(max 0 N+V) * normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ z)
        (actualSecondInheritedPuncture m γ) slots lists a labels (nonzeroChildFrequencyBall 1 R) (secondLabelWeight K)
        (clippedTest ω (Z^(max 0 N-N)) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
        (Z^(max 0 N)) Z (max 0 N+V) := by
  have he : secondLabelEnergy K labels (nonzeroChildFrequencyBall 1 R)
      (secondModeRight p hp hcop hg pool Ψ m z slots lists a ω (Z^N) t) γ =
      columnEnergy p hp hcop hg pool (secondRayPlus Ψ z) (actualSecondInheritedPuncture m γ)
        slots lists a labels (nonzeroChildFrequencyBall 1 R) (secondLabelWeight K)
        (childLogTest ω ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5)) (Z^N) := by
    unfold secondLabelEnergy columnEnergy
    apply Finset.sum_congr rfl
    intro f hf
    simp only [secondLabelWeight,secondModeRight,secondCanonicalPolynomial]
    apply congrArg (fun a : ℝ => ((idealDivisors f).card : ℝ)^(9+4*K)*a)
    exact child_ball_sum_neg (β:=ℝ) R (fun k => ‖finiteCanonicalMarkedRow p hp hcop hg pool
      (secondRayPlus Ψ z) (actualSecondInheritedPuncture m γ) (primaryGenerator f) k
      slots lists a (childLogTest ω ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5)) (Z^N)‖^2)
  rw [he]
  exact initial_columnEnergy_clipping_normalized p hp hcop hg pool (secondRayPlus Ψ z)
    (actualSecondInheritedPuncture m γ) slots lists a labels (nonzeroChildFrequencyBall 1 R)
    (secondLabelWeight K) ω hZ N V _

omit [DecidableEq σ] in
theorem normalized_child_energy_radical_puncture
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis) (D : Ideal Eis → ℝ)
    (W : ℝ → ℂ) (X Z F : ℝ) :
    normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D W X Z F =
    normalizedColumnEnergy p hp hcop hg pool Ψ
      (ConcretePrimeRowBridge.idealGenerator (Ideal.span {m}).radical)
      slots lists a labels rows D W X Z F := by
  unfold normalizedColumnEnergy
  apply Finset.sum_congr rfl
  intro f hf
  apply congrArg (fun x : ℝ => D f*x)
  apply Finset.sum_congr rfl
  intro k hk
  rw [finiteCanonicalMarkedRow_radical_puncture p hp hcop hg pool Ψ m (primaryGenerator f) k slots lists a W X]

end
end SevenEighths.InverseMoment

end OAI
