import OAI.Probability.FreeIsing.Estimates.FiniteWeightNormalization

namespace OAI

noncomputable section

namespace Problem367

theorem transitionKernel_tanh_eq_exp (beta : ℝ) (a b : IsingSpin) :
    transitionKernel (Real.tanh beta) a b =
      Real.exp (beta * spinSign a * spinSign b) / (2 * Real.cosh beta) := by
  have hc : Real.cosh beta ≠ 0 := ne_of_gt (Real.cosh_pos beta)
  cases a <;> cases b <;>
    simp only [transitionKernel, spinSign_neg, spinSign_pos, mul_neg, mul_one,
      neg_neg] <;>
    rw [Real.tanh_eq_sinh_div_cosh] <;>
    field_simp <;>
    nlinarith [Real.cosh_add_sinh beta, Real.cosh_sub_sinh beta]

theorem prod_transitionKernel_tanh_eq_exp
    {d : ℕ} (beta : ℝ) (D : Finset (TreeVertex d))
    (eta : TreeVertex d → IsingSpin) :
    (∏ e ∈ inducedEdges D, transitionKernel (Real.tanh beta) (eta e.1) (eta e.2)) =
      Real.exp (beta * ∑ e ∈ inducedEdges D, spinSign (eta e.1) * spinSign (eta e.2)) /
        (2 * Real.cosh beta) ^ (inducedEdges D).card := by
  simp_rw [transitionKernel_tanh_eq_exp]
  rw [Finset.prod_div_distrib, Finset.prod_const, ← Real.exp_sum]
  congr 2
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  ring

theorem freeCylinderWeight_tanh_eq_exp
    {d : ℕ} (beta : ℝ) (D : Finset (TreeVertex d))
    (eta : TreeVertex d → IsingSpin) :
    freeCylinderWeight (Real.tanh beta) D eta = ENNReal.ofReal
      (Real.exp (beta * ∑ e ∈ inducedEdges D, spinSign (eta e.1) * spinSign (eta e.2)) /
        (2 * (2 * Real.cosh beta) ^ (inducedEdges D).card)) := by
  rw [freeCylinderWeight_eq_transitionKernel, prod_transitionKernel_tanh_eq_exp]
  congr 1
  ring

theorem finiteIsing_partitionFunction
    {d : ℕ} (beta : ℝ) (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) :
    (∑ eta : D → IsingSpin, Real.exp (beta * ∑ e ∈ inducedEdges D,
      spinSign (extendFiniteSpin D eta e.1) * spinSign (extendFiniteSpin D eta e.2))) =
      2 * (2 * Real.cosh beta) ^ (inducedEdges D).card := by
  classical
  have hden : 0 < 2 * (2 * Real.cosh beta) ^ (inducedEdges D).card := by
    positivity
  have hn := sum_freeCylinderWeight_eq_one (Real.neg_one_lt_tanh beta).le
    (Real.tanh_lt_one beta).le D hD
  simp_rw [freeCylinderWeight_tanh_eq_exp] at hn
  rw [← ENNReal.ofReal_sum_of_nonneg (fun eta _ =>
    div_nonneg (Real.exp_pos _).le hden.le)] at hn
  have hreal := ENNReal.ofReal_eq_one.mp hn
  rw [← Finset.sum_div] at hreal
  exact (div_eq_one_iff_eq (ne_of_gt hden)).mp hreal

theorem finiteFreeIsingPMF_tanh_eq_normalized_exp
    {d : ℕ} (beta : ℝ) (D : Finset (TreeVertex d)) (hD : ConnectedFinset D)
    (eta : D → IsingSpin) :
    finiteFreeIsingPMF (Real.neg_one_lt_tanh beta).le (Real.tanh_lt_one beta).le D hD eta =
      ENNReal.ofReal (Real.exp (beta * ∑ e ∈ inducedEdges D,
        spinSign (extendFiniteSpin D eta e.1) * spinSign (extendFiniteSpin D eta e.2)) /
        (∑ xi : D → IsingSpin, Real.exp (beta * ∑ e ∈ inducedEdges D,
          spinSign (extendFiniteSpin D xi e.1) * spinSign (extendFiniteSpin D xi e.2)))) := by
  rw [finiteFreeIsingPMF_apply, freeCylinderWeight_tanh_eq_exp, finiteIsing_partitionFunction beta D hD]

theorem log_transitionKernel_tanh (beta : ℝ) (a b : IsingSpin) :
    Real.log (transitionKernel (Real.tanh beta) a b) =
      beta * spinSign a * spinSign b - Real.log (2 * Real.cosh beta) := by
  rw [transitionKernel_tanh_eq_exp, Real.log_div (ne_of_gt (Real.exp_pos _))
    (ne_of_gt (by positivity : 0 < 2 * Real.cosh beta)), Real.log_exp]

theorem freeCylinderWeight_tanh_pos
    {d : ℕ} (beta : ℝ) (D : Finset (TreeVertex d))
    (eta : TreeVertex d → IsingSpin) :
    0 < freeCylinderWeight (Real.tanh beta) D eta := by
  rw [freeCylinderWeight_tanh_eq_exp]
  exact ENNReal.ofReal_pos.mpr (by positivity)

theorem HasFreeIsingLaw.cylinder_boltzmann
    {d : ℕ} {beta : ℝ} {mu : MeasureTheory.Measure (TreeVertex d → IsingSpin)}
    (hmu : HasFreeIsingLaw (Real.tanh beta) mu)
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D)
    (eta : TreeVertex d → IsingSpin) :
    mu {x | ∀ v ∈ D, x v = eta v} = ENNReal.ofReal
      (Real.exp (beta * ∑ e ∈ inducedEdges D, spinSign (eta e.1) * spinSign (eta e.2)) /
        (2 * (2 * Real.cosh beta) ^ (inducedEdges D).card)) := by
  rw [hmu D hD eta, freeCylinderWeight_tanh_eq_exp]

end Problem367

end

end OAI
