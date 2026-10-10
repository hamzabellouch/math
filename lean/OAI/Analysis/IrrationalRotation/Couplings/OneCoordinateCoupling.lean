import OAI.Analysis.IrrationalRotation.Model.OneCoordinateCoupling
import OAI.Analysis.IrrationalRotation.Couplings.CouplingMarginalBounds
import OAI.Analysis.IrrationalRotation.Couplings.CouplingMixture

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Invariant233.OneCoordinateCoupling

open CouplingMarginalBounds CouplingMixture

instance baseLaw_isProbabilityMeasure : IsProbabilityMeasure baseLaw :=
  intervalLaw_isProbabilityMeasure (by norm_num)

lemma leftLaw_isProbabilityMeasure {m a b : ℝ}
    (hm : 0 < m) (ha0 : 0 < a) (ha1 : a ≤ 1 / 4)
    (hb0 : 0 < b) (hb1 : b ≤ 1 / 4) (i : Fin 5) :
    IsProbabilityMeasure (leftLaw m a b i) := by
  have hinv : 0 < 1 / m := one_div_pos.mpr hm
  fin_cases i <;> simp only [leftLaw] <;>
    apply intervalLaw_isProbabilityMeasure <;> linarith

lemma rightLaw_isProbabilityMeasure {m a b : ℝ}
    (hm : 2 ≤ m) (ha0 : 0 < a) (ha1 : a ≤ 1 / 4)
    (hb0 : 0 < b) (hb1 : b ≤ 1 / 4) (i : Fin 5) :
    IsProbabilityMeasure (rightLaw m a b i) := by
  have hm0 : 0 < m := by linarith
  have hinv : 0 < 1 / m := one_div_pos.mpr hm0
  fin_cases i <;> simp only [rightLaw] <;>
    apply intervalLaw_isProbabilityMeasure <;> linarith

lemma componentProbabilities_nonneg {κ m a b t : ℝ}
    (hκ : 0 ≤ κ) (hm : 0 < m) (ht : 0 ≤ t) (i : Fin 5) :
    0 ≤ componentProbabilities κ m a b t i := by
  fin_cases i <;>
    simp only [componentProbabilities]
  all_goals first | exact rho_nonneg hκ | exact div_nonneg ht hm.le

lemma pairLaw_isProbabilityMeasure {κ m a b t : ℝ}
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 100) (hm : 100 ≤ m)
    (ha : 1 / m ≤ a) (ha' : a ≤ 1 / 4)
    (hb : 1 / m ≤ b) (hb' : b ≤ 1 / 4)
    (ht0 : 0 ≤ t) (ht : t ≤ 1) : IsProbabilityMeasure (pairLaw κ m a b t) := by
  have hm0 : 0 < m := by linarith
  have ha0 := width_pos hm0 ha
  have hb0 := width_pos hm0 hb
  have : ∀ i, IsProbabilityMeasure (leftLaw m a b i) :=
    leftLaw_isProbabilityMeasure hm0 ha0 ha' hb0 hb'
  have : ∀ i, IsProbabilityMeasure (rightLaw m a b i) :=
    rightLaw_isProbabilityMeasure (by linarith) ha0 ha' hb0 hb'
  apply mixture_isProbabilityMeasure
  have hq0 : 0 ≤ diagonalMass κ m a b t :=
    le_trans (by norm_num) (diagonalMass_bounds hκ0 hκ hm ha ha' hb hb' ht0 ht).1
  have hp0 := componentProbabilities_nonneg (a := a) (b := b) hκ0 hm0 ht0
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hp0 i),
    ← ENNReal.ofReal_add hq0 (Finset.sum_nonneg (fun i _ => hp0 i))]
  have htotal : diagonalMass κ m a b t + ∑ i, componentProbabilities κ m a b t i = 1 := by
    simp only [componentProbabilities, Fin.sum_univ_succ, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero]
    unfold diagonalMass
    ring
  rw [htotal]
  norm_num

lemma replacement_ae_ordered {m a b : ℝ} (hm : 2 ≤ m) (i : Fin 5) :
    ∀ᵐ z ∂(leftLaw m a b i).prod (rightLaw m a b i), z.1 ≤ z.2 := by
  have hm0 : 0 < m := by linarith
  have hinv : 1 / m ≤ 1 / 2 := by
    apply (div_le_iff₀ hm0).2
    linarith
  fin_cases i <;>
    simp only [leftLaw, rightLaw]
  all_goals apply intervalLaw_pair_ordered
  all_goals linarith

lemma pairLaw_ae_ordered {κ m a b t : ℝ} (hm : 2 ≤ m) :
    ∀ᵐ z ∂pairLaw κ m a b t, z.1 ≤ z.2 := by
  apply mixture_ae
  · exact diagonal_ae (measurableSet_le measurable_fst measurable_snd) (fun _ => le_rfl)
  · exact replacement_ae_ordered hm

lemma pairLaw_fst {κ m a b t : ℝ} (hm : 2 ≤ m)
    (ha0 : 0 < a) (ha1 : a ≤ 1 / 4) (hb0 : 0 < b) (hb1 : b ≤ 1 / 4) :
    (pairLaw κ m a b t).fst =
      ENNReal.ofReal (diagonalMass κ m a b t) • baseLaw +
        ∑ i, ENNReal.ofReal (componentProbabilities κ m a b t i) • leftLaw m a b i := by
  have : ∀ i, IsProbabilityMeasure (rightLaw m a b i) :=
    rightLaw_isProbabilityMeasure hm ha0 ha1 hb0 hb1
  exact mixture_fst _ _ _ _ _

lemma pairLaw_snd {κ m a b t : ℝ} (hm : 2 ≤ m)
    (ha0 : 0 < a) (ha1 : a ≤ 1 / 4) (hb0 : 0 < b) (hb1 : b ≤ 1 / 4) :
    (pairLaw κ m a b t).snd =
      ENNReal.ofReal (diagonalMass κ m a b t) • baseLaw +
        ∑ i, ENNReal.ofReal (componentProbabilities κ m a b t i) • rightLaw m a b i := by
  have : ∀ i, IsProbabilityMeasure (leftLaw m a b i) :=
    leftLaw_isProbabilityMeasure (by linarith) ha0 ha1 hb0 hb1
  have : ∀ i, IsProbabilityMeasure (rightLaw m a b i) :=
    rightLaw_isProbabilityMeasure hm ha0 ha1 hb0 hb1
  exact mixture_snd _ _ _ _ _

lemma baseLaw_eq_restrict : baseLaw = volume.restrict (Ico (0 : ℝ) 1) := by
  simp [baseLaw, intervalLaw, ProbabilityTheory.cond, Real.volume_Ico]

lemma interval_subset_unit {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    Ico a b ⊆ Ico (0 : ℝ) 1 := by
  intro x hx
  exact ⟨ha.trans hx.1, hx.2.trans_le hb⟩

lemma baseLaw_interval_measure {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a ≤ b) :
    baseLaw.real (Ico a b) = b - a := by
  rw [measureReal_def, baseLaw_eq_restrict, Measure.restrict_apply measurableSet_Ico,
    inter_eq_left.mpr (interval_subset_unit ha hb), Real.volume_Ico,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]

lemma intervalLaw_eq_base_cond {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    intervalLaw a b = baseLaw[|Ico a b] := by
  rw [baseLaw_eq_restrict]
  simp only [intervalLaw, ProbabilityTheory.cond,
    Measure.restrict_apply measurableSet_Ico,
    Measure.restrict_restrict measurableSet_Ico,
    inter_eq_left.mpr (interval_subset_unit ha hb)]

lemma intervalLaw_eq_base_withDensity {a b : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a < b) :
    intervalLaw a b = baseLaw.withDensity (fun x =>
      ENNReal.ofReal (uniformDensity baseLaw (Ico a b) x)) := by
  rw [intervalLaw_eq_base_cond ha hb]
  apply cond_eq_withDensity_uniformDensity measurableSet_Ico
  rw [baseLaw_interval_measure ha hb hab.le]
  exact sub_pos.mpr hab

lemma labelledLaw_map_snd (κ m a b t : ℝ) :
    (labelledLaw κ m a b t).map Prod.snd = pairLaw κ m a b t :=
  labelledMixture_map_snd _ _ _ _ _

lemma labelledLaw_isProbabilityMeasure {κ m a b t : ℝ}
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 100) (hm : 100 ≤ m)
    (ha : 1 / m ≤ a) (ha' : a ≤ 1 / 4)
    (hb : 1 / m ≤ b) (hb' : b ≤ 1 / 4)
    (ht0 : 0 ≤ t) (ht : t ≤ 1) : IsProbabilityMeasure (labelledLaw κ m a b t) := by
  have := pairLaw_isProbabilityMeasure hκ0 hκ hm ha ha' hb hb' ht0 ht
  constructor
  have h := congrArg (fun ν : Measure (ℝ × ℝ) => ν Set.univ)
    (labelledLaw_map_snd κ m a b t)
  simpa [Measure.map_apply measurable_snd MeasurableSet.univ] using h

lemma labelledLaw_tag_mass {κ m a b t : ℝ} (hm : 2 ≤ m)
    (ha0 : 0 < a) (ha1 : a ≤ 1 / 4) (hb0 : 0 < b) (hb1 : b ≤ 1 / 4) :
    labelledLaw κ m a b t {z | z.1 = some (4 : Fin 5)} = ENNReal.ofReal (t / m) := by
  have : ∀ i, IsProbabilityMeasure (leftLaw m a b i) :=
    leftLaw_isProbabilityMeasure (by linarith) ha0 ha1 hb0 hb1
  have : ∀ i, IsProbabilityMeasure (rightLaw m a b i) :=
    rightLaw_isProbabilityMeasure hm ha0 ha1 hb0 hb1
  exact labelledMixture_some_mass _ _ _ _ _ (4 : Fin 5)

lemma labelledLaw_diagonal_mass (κ m a b t : ℝ) :
    labelledLaw κ m a b t {z | z.1 = none} = ENNReal.ofReal (diagonalMass κ m a b t) :=
  labelledMixture_none_mass _ _ _ _ _

lemma labelledLaw_ae_ordered {κ m a b t : ℝ} (hm : 2 ≤ m) :
    ∀ᵐ z ∂labelledLaw κ m a b t, z.2.1 ≤ z.2.2 := by
  have h := pairLaw_ae_ordered (κ := κ) (a := a) (b := b) (t := t) hm
  rw [← labelledLaw_map_snd] at h
  exact (ae_map_iff measurable_snd.aemeasurable
    (measurableSet_le measurable_fst measurable_snd)).1 h

end Invariant233.OneCoordinateCoupling

end OAI
