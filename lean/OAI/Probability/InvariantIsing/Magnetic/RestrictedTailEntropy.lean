import OAI.Probability.InvariantIsing.Magnetic.RestrictedTailSpinKernel
import OAI.Probability.InvariantIsing.Magnetic.RestrictedFieldOrder

namespace OAI

/-! The entropy of the complete constrained sampling law is bounded by
its actual recursion loss, uniformly in the number of levels. -/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory IsingPerceptron
open scoped NNReal ENNReal

namespace InvariantIsing

theorem restrictedTailSpinKernel_entropy {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : ∀ i < n, 0 < b i) (hb1 : ∀ i < n, b i ≤ 1) (z : Fin N → ℝ) :
    klDiv (restrictedTailSpinKernel hN S hS n b v hb z)
      (restrictedTailSpinKernel hN Finset.univ Finset.univ_nonempty n b v hb z) ≤
        ENNReal.ofReal (restrictedFieldRecursion Finset.univ n b v z -
          restrictedFieldRecursion S n b v z) := by
  induction n generalizing b v z with
  | zero =>
    change klDiv (restrictedSpinKernel S z) (restrictedSpinKernel Finset.univ z) ≤ _
    rw [restrictedSpinKernel_univ]
    have he := restrictedSpinKernel_entropy S hS z
    rw [← ENNReal.ofReal_toReal he.1, he.2]
    rfl
  | succ n ih =>
    let bs := fun i => b (i + 1)
    let vs := fun i => v (i + 1)
    have hbs : ∀ i < n, 0 < bs i := fun i hi => hb (i + 1) (by omega)
    have hbs1 : ∀ i < n, bs i ≤ 1 := fun i hi => hb1 (i + 1) (by omega)
    let F := restrictedFieldRecursion (Finset.univ : Finset (Spin N)) n bs vs
    let G := restrictedFieldRecursion S n bs vs
    have hF := restrictedFieldRecursion_regular hN Finset.univ Finset.univ_nonempty n bs vs hbs
    have hG := restrictedFieldRecursion_regular hN S hS n bs vs hbs
    let κ := restrictedTailSpinKernel hN S hS n bs vs hbs
    let η := restrictedTailSpinKernel hN Finset.univ Finset.univ_nonempty n bs vs hbs
    have hac (y : Fin N → ℝ) : κ y ≪ η y :=
      (klDiv_ne_top_iff.mp (ne_top_of_le_ne_top ENNReal.ofReal_ne_top
        (ih bs vs hbs hbs1 y))).1
    have hκ (y : Fin N → ℝ) : kernelRelativeEntropy κ η y ≤ ENNReal.ofReal (F y - G y) := by
      rw [kernelRelativeEntropy_eq κ η y (hac y)]
      exact ih bs vs hbs hbs1 y
    have hg := vectorGaussianTransition_entropy_budget hN (b 0) (hb 0 (by omega))
      (hb1 0 (by omega)) (v 0) F G hF.1 hG.1 hF.2 hG.2
      (fun y => restrictedFieldRecursion_mono hN S Finset.univ hS Finset.univ_nonempty
        (Finset.subset_univ S) n bs vs hbs y) z
    have he := entropy_budget_drop
      (vectorGaussianTransition N (b 0) (v 0) G hG.1 z)
      (vectorGaussianTransition N (b 0) (v 0) F hF.1 z) κ η hac
      (fun y => ENNReal.ofReal (F y - G y)) hκ
    rw [Measure.comp_eq_comp_const_apply, Measure.comp_eq_comp_const_apply] at he
    exact he.trans hg

end InvariantIsing

end

end OAI
