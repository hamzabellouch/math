import OAI.Analysis.IrrationalRotation.Model.PrefixDomination
import OAI.Analysis.IrrationalRotation.Product.OneCoordinateDensity
import OAI.Analysis.IrrationalRotation.Product.FiniteProductAbsoluteContinuity

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace Invariant233.CouplingMixture

lemma intervalLaw_pair_strictly_ordered {a b c d : ℝ} (hbc : b ≤ c) :
    ∀ᵐ z ∂(intervalLaw a b).prod (intervalLaw c d), z.1 < z.2 := by
  have : IsZeroOrProbabilityMeasure (intervalLaw a b) := inferInstanceAs
    (IsZeroOrProbabilityMeasure (volume[|Ico a b]))
  have : IsZeroOrProbabilityMeasure (intervalLaw c d) := inferInstanceAs
    (IsZeroOrProbabilityMeasure (volume[|Ico c d]))
  rw [Measure.ae_prod_iff_ae_ae (measurableSet_lt measurable_fst measurable_snd)]
  filter_upwards [intervalLaw_ae_mem a b] with x hx
  filter_upwards [intervalLaw_ae_mem c d] with y hy
  exact hx.2.trans_le (hbc.trans hy.1)

end Invariant233.CouplingMixture

namespace Invariant233.OneCoordinateCoupling

open CouplingMixture

instance triangleLaw_isFiniteMeasure : IsFiniteMeasure triangleLaw := by
  unfold triangleLaw
  infer_instance

lemma replacement_ae_strictly_ordered {m a b : ℝ} (hm : 2 ≤ m) (i : Fin 5) :
    ∀ᵐ z ∂(leftLaw m a b i).prod (rightLaw m a b i), z.1 < z.2 := by
  have hm0 : 0 < m := by linarith
  have hinv : 1 / m ≤ 1 / 2 := (div_le_iff₀ hm0).2 (by linarith)
  fin_cases i <;> simp only [leftLaw, rightLaw]
  all_goals apply intervalLaw_pair_strictly_ordered
  all_goals linarith

lemma replacementDensity_measurable (m a b : ℝ) (i : Fin 5) :
    Measurable (replacementDensity m a b i) := by
  have hl : Measurable (fun x => ENNReal.ofReal (leftDensity m a b i x)) := by
    apply Measurable.ennreal_ofReal
    fin_cases i <;> exact intervalDensity_measurable _ _
  have hr : Measurable (fun x => ENNReal.ofReal (rightDensity m a b i x)) := by
    apply Measurable.ennreal_ofReal
    fin_cases i <;> exact intervalDensity_measurable _ _
  exact (hl.comp measurable_fst).mul (hr.comp measurable_snd)

lemma replacement_eq_triangle_withDensity {m a b : ℝ} (hm : 2 ≤ m)
    (ha0 : 0 < a) (ha1 : a ≤ 1 / 4) (hb0 : 0 < b) (hb1 : b ≤ 1 / 4)
    (i : Fin 5) :
    (leftLaw m a b i).prod (rightLaw m a b i) =
      triangleLaw.withDensity (replacementDensity m a b i) := by
  have hl : Measurable (fun x => ENNReal.ofReal (leftDensity m a b i x)) := by
    apply Measurable.ennreal_ofReal
    fin_cases i <;> exact intervalDensity_measurable _ _
  have hr : Measurable (fun x => ENNReal.ofReal (rightDensity m a b i x)) := by
    apply Measurable.ennreal_ofReal
    fin_cases i <;> exact intervalDensity_measurable _ _
  have hd : (leftLaw m a b i).prod (rightLaw m a b i) =
      (baseLaw.prod baseLaw).withDensity (replacementDensity m a b i) := by
    rw [leftLaw_eq_withDensity hm ha0 ha1 hb0 hb1,
      rightLaw_eq_withDensity hm ha0 ha1 hb0 hb1, prod_withDensity hl hr]
    rfl
  have hs : ((leftLaw m a b i).prod (rightLaw m a b i)).restrict
      {z : ℝ × ℝ | z.1 < z.2} = (leftLaw m a b i).prod (rightLaw m a b i) :=
    Measure.restrict_eq_self_of_ae_mem
      (replacement_ae_strictly_ordered (a := a) (b := b) hm i)
  rw [hd, restrict_withDensity (measurableSet_lt measurable_fst measurable_snd)] at hs
  exact hd.trans hs.symm

lemma replacement_absolutelyContinuous_triangle {m a b : ℝ} (hm : 2 ≤ m)
    (ha0 : 0 < a) (ha1 : a ≤ 1 / 4) (hb0 : 0 < b) (hb1 : b ≤ 1 / 4)
    (i : Fin 5) :
    (leftLaw m a b i).prod (rightLaw m a b i) ≪ triangleLaw := by
  rw [replacement_eq_triangle_withDensity hm ha0 ha1 hb0 hb1]
  exact withDensity_absolutelyContinuous _ _

lemma componentLaw_absolutelyContinuous {m a b : ℝ} (hm : 2 ≤ m)
    (ha0 : 0 < a) (ha1 : a ≤ 1 / 4) (hb0 : 0 < b) (hb1 : b ≤ 1 / 4)
    (l : Option (Fin 5)) : componentLaw m a b l ≪ componentReference l := by
  cases l with
  | none => exact Measure.AbsolutelyContinuous.rfl
  | some i => exact replacement_absolutelyContinuous_triangle hm ha0 ha1 hb0 hb1 i

lemma pairLaw_absolutelyContinuous_diagonal_add_triangle {κ m a b t : ℝ}
    (hm : 2 ≤ m) (ha0 : 0 < a) (ha1 : a ≤ 1 / 4)
    (hb0 : 0 < b) (hb1 : b ≤ 1 / 4) :
    pairLaw κ m a b t ≪ diagonal baseLaw + triangleLaw := by
  unfold pairLaw mixture
  apply Measure.AbsolutelyContinuous.add_left
  · exact (Measure.AbsolutelyContinuous.rfl.add_right triangleLaw).smul_left _
  · rw [← Measure.sum_fintype]
    apply Measure.absolutelyContinuous_sum_left
    intro i
    exact ((replacement_absolutelyContinuous_triangle hm ha0 ha1 hb0 hb1 i).add_right'
      (diagonal baseLaw)).smul_left _

lemma finite_pairLaws_domination {n : ℕ} (κ m a b t : Fin n → ℝ)
    (hm : ∀ i, 2 ≤ m i) (ha0 : ∀ i, 0 < a i) (ha1 : ∀ i, a i ≤ 1 / 4)
    (hb0 : ∀ i, 0 < b i) (hb1 : ∀ i, b i ≤ 1 / 4)
    [∀ i, IsFiniteMeasure (pairLaw (κ i) (m i) (a i) (b i) (t i))] :
    Measure.pi (fun i => pairLaw (κ i) (m i) (a i) (b i) (t i)) ≪
      ∑ pattern : Fin n → Bool,
        Measure.pi (fun i => if pattern i then triangleLaw else diagonal baseLaw) := by
  rw [← Invariant233.pi_add_eq_sum_bool
    (fun _ : Fin n => diagonal baseLaw) (fun _ => triangleLaw)]
  apply Invariant233.fin_pi_absolutelyContinuous
  intro i
  exact pairLaw_absolutelyContinuous_diagonal_add_triangle
    (hm i) (ha0 i) (ha1 i) (hb0 i) (hb1 i)

end Invariant233.OneCoordinateCoupling

end

end OAI
