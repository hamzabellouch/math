import OAI.Probability.InvariantIsing.Magnetic.RestrictedPairSpinKernel

namespace OAI

/-! The entropy cost of a branching pair is at most twice the scalar
block loss, independently of the split level or number of levels. -/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory IsingPerceptron
open scoped NNReal ENNReal

namespace InvariantIsing

theorem restrictedPairSpinKernel_entropy {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : ∀ j < n, 0 < b j) (hb1 : ∀ j < n, b j ≤ 1)
    (i : Fin (n + 1)) (z : Fin N → ℝ) :
    klDiv (restrictedPairSpinKernel hN S hS n b v hb i z)
      (restrictedPairSpinKernel hN Finset.univ Finset.univ_nonempty n b v hb i z) ≤
        2 * ENNReal.ofReal (restrictedFieldRecursion Finset.univ n b v z -
          restrictedFieldRecursion S n b v z) := by
  let _ := restrictedSpinKernel_markov S hS
  let _ := restrictedSpinKernel_markov (Finset.univ : Finset (Spin N)) Finset.univ_nonempty
  have htail (m : ℕ) (c : ℕ → ℝ) (w : ℕ → ℝ≥0) (hc : ∀ j < m, 0 < c j)
      (hc1 : ∀ j < m, c j ≤ 1) (y : Fin N → ℝ) :
      klDiv ((restrictedTailSpinKernel hN S hS m c w hc y).prod
          (restrictedTailSpinKernel hN S hS m c w hc y))
        ((restrictedTailSpinKernel hN Finset.univ Finset.univ_nonempty m c w hc y).prod
          (restrictedTailSpinKernel hN Finset.univ Finset.univ_nonempty m c w hc y)) ≤
      2 * ENNReal.ofReal (restrictedFieldRecursion Finset.univ m c w y -
          restrictedFieldRecursion S m c w y) := by
    have he := restrictedTailSpinKernel_entropy hN S hS m c w hc hc1 y
    have hac := (klDiv_ne_top_iff.mp (ne_top_of_le_ne_top ENNReal.ofReal_ne_top he)).1
    rw [klDiv_prod_self _ _ hac]
    exact mul_le_mul_right he 2
  induction n generalizing b v z with
  | zero =>
    change klDiv ((_ ×ₖ _) z) ((_ ×ₖ _) z) ≤ _
    simpa only [restrictedTailSpinKernel, Kernel.prod_apply] using htail 0 b v hb hb1 z
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · change klDiv ((_ ×ₖ _) z) ((_ ×ₖ _) z) ≤ _
      simp only [Kernel.prod_apply]
      exact htail (n + 1) b v hb hb1 z
    · let bs := fun j => b (j + 1)
      let vs := fun j => v (j + 1)
      have hbs : ∀ j < n, 0 < bs j := fun j hj => hb (j + 1) (by omega)
      have hbs1 : ∀ j < n, bs j ≤ 1 := fun j hj => hb1 (j + 1) (by omega)
      let F := restrictedFieldRecursion (Finset.univ : Finset (Spin N)) n bs vs
      let G := restrictedFieldRecursion S n bs vs
      have hF := restrictedFieldRecursion_regular hN Finset.univ Finset.univ_nonempty n bs vs hbs
      have hG := restrictedFieldRecursion_regular hN S hS n bs vs hbs
      let κ := restrictedPairSpinKernel hN S hS n bs vs hbs j
      let η := restrictedPairSpinKernel hN Finset.univ Finset.univ_nonempty n bs vs hbs j
      have hi (y : Fin N → ℝ) := ih bs vs hbs hbs1 j y
      have hac (y : Fin N → ℝ) : κ y ≪ η y :=
        (klDiv_ne_top_iff.mp (ne_top_of_le_ne_top (by finiteness) (hi y))).1
      have hκ (y : Fin N → ℝ) : kernelRelativeEntropy κ η y ≤
          2 * ENNReal.ofReal (F y - G y) := by
        rw [kernelRelativeEntropy_eq κ η y (hac y)]
        exact hi y
      have hg := vectorGaussianTransition_entropy_budget hN (b 0) (hb 0 (by omega))
        (hb1 0 (by omega)) (v 0) F G hF.1 hG.1 hF.2 hG.2
        (fun y => restrictedFieldRecursion_mono hN S Finset.univ hS Finset.univ_nonempty
          (Finset.subset_univ S) n bs vs hbs y) z
      have he := entropy_budget_drop
        (vectorGaussianTransition N (b 0) (v 0) G hG.1 z)
        (vectorGaussianTransition N (b 0) (v 0) F hF.1 z) κ η hac
        (fun y => 2 * ENNReal.ofReal (F y - G y)) hκ
      rw [lintegral_const_mul 2 (f := fun y => ENNReal.ofReal (F y - G y))
        (hF.1.sub hG.1).ennreal_ofReal] at he
      rw [Measure.comp_eq_comp_const_apply, Measure.comp_eq_comp_const_apply] at he
      exact he.trans (entropy_budget_double hg)

end InvariantIsing

end

end OAI
