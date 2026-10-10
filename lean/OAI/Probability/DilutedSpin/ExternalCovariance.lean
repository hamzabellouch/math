import OAI.Probability.DilutedSpin.ExternalAverageTaylor
import OAI.Probability.DilutedSpin.SingletonRoot

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

 
noncomputable def externalCovariance (t u : ℝ) : ℝ :=
  externalAverage ξ μ ν η r s S a T Q m base old D E f t u -
    oldTreeAverage ξ μ ν r s S T Q (fun j => m j.succ) base old f *
      externalAverage ξ μ ν η r s S a T Q m base old D E (fun _ => 1) t u

noncomputable def covarianceCoefficient (k : ℕ) : ℝ :=
  externalCoefficientAverage ξ μ ν η r s S a T Q m base old D E f k -
    oldTreeAverage ξ μ ν r s S T Q (fun j => m j.succ) base old f *
      externalCoefficientAverage ξ μ ν η r s S a T Q m base old D E (fun _ => 1) k

variable (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    (hm : ∀ j : Fin L, m j.succ ≠ 0) (hmono : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hroot : m 0 = 0) (hend : m (Fin.last L) = 1)
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B)
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)

include hb hm hmono hpos hroot hend hB hf hD hE in
lemma externalCovariance_taylor_bound {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) (1/2)) (k : ℕ) :
    |externalCovariance ξ μ ν η r s S a T Q m base old D E f t 0 -
      ∑ j ∈ Finset.range (k+1), covarianceCoefficient ξ μ ν η r s S a T Q m base old D E f j*t^j| ≤
        (2*B*PrescribedTree.derivativeBound (S.leaves+(Finset.univ.erase a).card) (k+1)/(k.factorial:ℝ))*t^(k+1) := by
  have h1 := externalAverage_taylor_bound ξ μ ν η r s S a T Q m base old D E f hb hm hmono hpos hroot hend hB hf hD hE ht k
  have h2 := externalAverage_taylor_bound ξ μ ν η r s S a T Q m base old D E (fun _ => 1) hb hm hmono hpos hroot hend
    (by norm_num : (0:ℝ) ≤ 1) (by intro _; norm_num) hD hE ht k
  have hmean := oldTreeAverage_bound ξ μ ν r s S T Q (fun j => m j.succ) base old f hf
  let c := oldTreeAverage ξ μ ν r s S T Q (fun j => m j.succ) base old f
  let F := externalAverage ξ μ ν η r s S a T Q m base old D E f t 0
  let G := externalAverage ξ μ ν η r s S a T Q m base old D E (fun _ => 1) t 0
  let P := ∑ j ∈ Finset.range (k+1), externalCoefficientAverage ξ μ ν η r s S a T Q m base old D E f j*t^j
  let R := ∑ j ∈ Finset.range (k+1), externalCoefficientAverage ξ μ ν η r s S a T Q m base old D E (fun _ => 1) j*t^j
  have he : externalCovariance ξ μ ν η r s S a T Q m base old D E f t 0 -
      ∑ j ∈ Finset.range (k+1), covarianceCoefficient ξ μ ν η r s S a T Q m base old D E f j*t^j = (F-P)-c*(G-R) := by
    simp only [externalCovariance,covarianceCoefficient,sub_mul,Finset.sum_sub_distrib,mul_assoc,← Finset.mul_sum]
    dsimp only [F,P,c,G,R]
    ring
  rw [he]
  have hh := (abs_sub (F-P) (c*(G-R))).trans (add_le_add h1 (show |c*(G-R)| ≤ B*((1*PrescribedTree.derivativeBound (S.leaves+(Finset.univ.erase a).card) (k+1)/(k.factorial:ℝ))*t^(k+1)) from by
    rw [abs_mul]
    exact mul_le_mul hmean h2 (abs_nonneg _) hB))
  calc
    _ ≤ (B*PrescribedTree.derivativeBound (S.leaves+(Finset.univ.erase a).card) (k+1)/(k.factorial:ℝ))*t^(k+1) +
        B*((1*PrescribedTree.derivativeBound (S.leaves+(Finset.univ.erase a).card) (k+1)/(k.factorial:ℝ))*t^(k+1)) := hh
    _ = _ := by ring

include hb hm hmono hpos hroot hend hB hf hD hE in
lemma externalCovariance_sub_le {t u : ℝ} (ht : |t| ≤ 1/4) (huz : 0 ≤ u) (hu : u ≤ 1/4) :
    |externalCovariance ξ μ ν η r s S a T Q m base old D E f t u -
      externalCovariance ξ μ ν η r s S a T Q m base old D E f t 0| ≤ 2*(4+8*(S.leaves:ℝ))*B*u := by
  have h1 := externalAverage_sub_le ξ μ ν η r s S a T Q m base old D E f hb hm hmono hpos hroot hend hB hf hD hE ht huz hu
  have h2 := externalAverage_sub_le ξ μ ν η r s S a T Q m base old D E (fun _ => 1) hb hm hmono hpos hroot hend
    (by norm_num : (0:ℝ) ≤ 1) (by intro _; norm_num) hD hE ht huz hu
  have hmean := oldTreeAverage_bound ξ μ ν r s S T Q (fun j => m j.succ) base old f hf
  unfold externalCovariance
  rw [show ∀ F G F' G' c : ℝ, (F-c*G)-(F'-c*G')=(F-F')-c*(G-G') by intros; ring]
  refine (abs_sub _ _).trans ?_
  rw [abs_mul]
  have hh := mul_le_mul hmean h2 (abs_nonneg _) hB
  linarith

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
