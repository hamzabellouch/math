import OAI.Probability.DilutedSpin.ExternalRoot
import OAI.Probability.DilutedSpin.PatternComparison

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}
variable (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν η : Measure I) [IsProbabilityMeasure ν] [IsProbabilityMeasure η]
    (r s : ℝ≥0) (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    (hm : ∀ j : Fin L, m j.succ ≠ 0) (hmono : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hroot : m 0 = 0) (hend : m (Fin.last L) = 1)
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B)
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)

lemma affine_one_lower {d t : ℝ} (hd : |d| ≤ 1) (ht : t ∈ Set.Icc (0:ℝ) (1/2)) :
    1/2 ≤ 1+t*d := by
  have hd0 := (abs_le.mp hd).1
  rcases ht with ⟨ht0,ht1⟩
  nlinarith [mul_nonneg ht0 (show 0 ≤ d+1 by linarith)]

lemma affine_two_lower {d e t u : ℝ} (hd : |d| ≤ 1) (he : |e| ≤ 1)
    (ht : |t| ≤ 1/4) (hu : |u| ≤ 1/4) : 1/2 ≤ 1+t*d+u*e := by
  have htd : |t*d| ≤ 1/4 := by rw [abs_mul]; nlinarith [abs_nonneg t,abs_nonneg d]
  have hue : |u*e| ≤ 1/4 := by rw [abs_mul]; nlinarith [abs_nonneg u,abs_nonneg e]
  linarith [(abs_le.mp htd).1,(abs_le.mp hue).1]

include hb hm hmono hpos hroot hend hB hf hD hE in
/-- Full finite-volume disorder averaging of the uniform all-order Taylor
bound. Physical fields, physical Poisson terms and the entire countable
reservoir are unchanged as the new insertion parameter varies. -/
theorem externalAverage_taylor_bound {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) (1/2)) (k : ℕ) :
    |externalAverage ξ μ ν η r s S a T Q m base old D E f t 0 -
      ∑ j ∈ Finset.range (k+1), externalCoefficientAverage ξ μ ν η r s S a T Q m base old D E f j*t^j| ≤
        (B*PrescribedTree.derivativeBound (S.leaves+(Finset.univ.erase a).card) (k+1)/(k.factorial:ℝ))*t^(k+1) := by
  unfold externalAverage externalCoefficientAverage
  simp only [zero_mul, add_zero]
  apply integral_polynomial_remainder
  · exact integrable_rootExternalTreeScore ξ μ ν η r s S a T Q m base old E f hb hf hE _
      (fun i x y => affine_one_lower (hD i x y) ht)
  · intro j
    exact integrable_rootExternalCoefficient ξ μ ν η r s S a T Q m base old D E f hb hm hmono hpos hroot hend hB hf hD hE j
  · intro z
    exact externalTreeScore_taylor_bound S a T Q m hm hmono hpos hroot hend
      (base z.1.1 z.1.2.1.1 z.1.2.1.2) (rootArray z.1.2.2.1 z.1.2.2.2) z.2 old (D z.2) (E z.2) f hB hf (hD z.2) (hE z.2) ht k

include hb hm hmono hpos hroot hend hB hf hD hE in
theorem externalAverage_sub_le {t u : ℝ} (ht : |t| ≤ 1/4) (huz : 0 ≤ u) (hu : u ≤ 1/4) :
    |externalAverage ξ μ ν η r s S a T Q m base old D E f t u -
      externalAverage ξ μ ν η r s S a T Q m base old D E f t 0| ≤ (4+8*(S.leaves:ℝ))*B*u := by
  unfold externalAverage
  simp only [zero_mul, add_zero]
  apply integral_difference_bound
  · exact integrable_rootExternalTreeScore ξ μ ν η r s S a T Q m base old E f hb hf hE _
      (fun i x y => affine_two_lower (hD i x y) (hE i x y) ht (by rwa [abs_of_nonneg huz]))
  · exact integrable_rootExternalTreeScore ξ μ ν η r s S a T Q m base old E f hb hf hE _
      (fun i x y => by simpa only [zero_mul,add_zero] using affine_two_lower (hD i x y) (hE i x y) ht (show |(0:ℝ)| ≤ 1/4 by norm_num))
  · intro z
    exact externalTreeScore_sub_le S a T Q m hm hmono hpos hroot hend
      (base z.1.1 z.1.2.1.1 z.1.2.1.2) (rootArray z.1.2.2.1 z.1.2.2.2) z.2 old (D z.2) (E z.2) f hB hf (hD z.2) (hE z.2) ht huz hu

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
