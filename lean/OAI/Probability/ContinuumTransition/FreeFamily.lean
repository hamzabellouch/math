import OAI.Probability.ContinuumTransition.RootVolume

namespace OAI

section
open scoped BigOperators ENNReal
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

lemma measurableSet_freeConfig {ι : Type} [Fintype ι] (t : ℝ) :
    MeasurableSet {x : ι → Space | FreeConfig t x} := by
  apply measurableSet_forall_labels
  intro i
  apply measurableSet_forall_labels
  intro j
  by_cases hij : i = j
  · simp only [hij, ne_eq, not_true_eq_false, false_implies, ofPred_true, MeasurableSet.univ]
  have hm : Measurable (fun x : ι → Space => ‖x i-x j‖) :=
    ((measurable_pi_apply i).sub (measurable_pi_apply j)).norm
  have he : {x : ι → Space | i ≠ j → ‖x i-x j‖ < 1 →
      Real.exp (-t) ≤ ‖x i-x j‖ ∧ ‖x i-x j‖ ≤ (1+shellDelta)*Real.exp (-t)} =
      {x | 1 ≤ ‖x i-x j‖} ∪
      ({x | Real.exp (-t) ≤ ‖x i-x j‖} ∩ {x | ‖x i-x j‖ ≤ (1+shellDelta)*Real.exp (-t)}) := by
    ext x
    simp only [mem_ofPred_eq, mem_union, mem_inter_iff, ne_eq, hij, not_false_eq_true, imp_iff_not_or, not_lt, not_true_eq_false, false_or]
  rw [he]
  exact (measurableSet_le measurable_const hm).union
    ((measurableSet_le measurable_const hm).inter (measurableSet_le hm measurable_const))

noncomputable def freeFamily (t d : ℝ) : ConfigFamily :=
  fun ι _ x => if FreeConfig t x then Real.exp (d*Fintype.card ι) else 0

lemma freeFamily_relabel (t d : ℝ) : RelabelInvariant (freeFamily t d) := by
  intro ι κ _ _ e x
  have he : FreeConfig t (x ∘ e) ↔ FreeConfig t x := by
    constructor
    · intro hh i j hij hdist
      have hn : e.symm i ≠ e.symm j := fun he => hij (e.symm.injective he)
      simpa only [Function.comp_apply, Equiv.apply_symm_apply] using
        hh (e.symm i) (e.symm j) hn (by simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hdist)
    · intro hh i j hij hdist
      exact hh (e i) (e j) (fun he => hij (e.injective he)) hdist
  simp only [freeFamily, he, Fintype.card_congr e]

lemma freeFamily_measurable (t d : ℝ) (ι : Type) [Fintype ι] : Measurable (freeFamily t d ι) :=
  Measurable.ite (measurableSet_freeConfig t) measurable_const measurable_const

lemma freeFamily_nonneg (t d : ℝ) (ι : Type) [Fintype ι] (x : ι → Space) :
    0 ≤ freeFamily t d ι x := by
  unfold freeFamily
  split_ifs <;> positivity

lemma freeFamily_le_exp (t d : ℝ) (ι : Type) [Fintype ι] (x : ι → Space) :
    freeFamily t d ι x ≤ Real.exp (d*Fintype.card ι) := by
  unfold freeFamily
  split_ifs
  · exact le_rfl
  · exact (Real.exp_pos _).le

lemma freeFamily_summable (t d L : ℝ) : Summable (familyTerm (freeFamily t d) (cube L)) :=
  summable_familyTerm_of_bound _ (isCompact_cube L).measure_lt_top.ne (freeFamily_measurable t d)
    (freeFamily_nonneg t d) (freeFamily_le_exp t d)

lemma rootCover_volume_real {ι : Type} [Fintype ι] (s : Finset ι) (r L : ℝ) :
    volume.real ({x : ι → Space | ∀ i, x i ∈ cube L} ∩ rootCover s r) ≤
      (volume.real (cube L))^s.card *
        ((s.card : ℝ)*volume.real (Metric.closedBall (0 : Space) r))^(Fintype.card ι-s.card) := by
  have hh := ENNReal.toReal_mono (show
    (volume (cube L))^s.card *
      ((s.card : ℝ≥0∞)*volume (Metric.closedBall (0 : Space) r))^(Fintype.card ι-s.card) ≠ ⊤ by
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top (isCompact_cube L).measure_lt_top.ne)
      (ENNReal.pow_ne_top (ENNReal.mul_ne_top (by simp) (measure_closedBall_lt_top.ne)))) (rootCover_volume s r L)
  simpa only [Measure.real, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast] using hh

lemma freeConfig_volume_le {ι : Type} [Fintype ι] {t : ℝ}
    (ht : 2*(1+shellDelta)*Real.exp (-t) < 1) (L : ℝ) :
    volume.real ({x : ι → Space | ∀ i, x i ∈ cube L} ∩ {x | FreeConfig t x}) ≤
      ∑ k ∈ Finset.range (Fintype.card ι+1),
        if k ≤ packingNumber L ∧ Fintype.card ι ≤ 4*k then
          ((Fintype.card ι).choose k : ℝ)*(volume.real (cube L))^k *
            ((k : ℝ)*volume.real (Metric.closedBall (0 : Space) ((1+shellDelta)*Real.exp (-t))))^(Fintype.card ι-k)
        else 0 := by
  let T : Finset (Finset ι) := Finset.univ.filter (fun s => s.card ≤ packingNumber L ∧ Fintype.card ι ≤ 4*s.card)
  let A : Finset ι → Set (ι → Space) := fun s =>
    {x | ∀ i, x i ∈ cube L} ∩ rootCover s ((1+shellDelta)*Real.exp (-t))
  have hsub : ({x : ι → Space | ∀ i, x i ∈ cube L} ∩ {x | FreeConfig t x}) ⊆ ⋃ s ∈ T, A s := by
    intro x hx
    obtain ⟨s,hs,hn,hc⟩ := freeConfig_roots ht hx.2 hx.1
    apply mem_iUnion₂.mpr
    refine ⟨s,by simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hs,hn⟩,hx.1,?_⟩
    intro j
    obtain ⟨i,hi,hij⟩ := hc j
    exact ⟨⟨i,hi⟩,hij⟩
  have hfin : volume (⋃ s ∈ T, A s) ≠ ⊤ := by
    apply ne_top_of_le_ne_top (show volume {x : ι → Space | ∀ i, x i ∈ cube L} ≠ ⊤ by
      rw [volume_generalConfigurations]; exact ENNReal.pow_ne_top (isCompact_cube L).measure_lt_top.ne)
    apply measure_mono
    intro x hx
    obtain ⟨s,_,hs⟩ := mem_iUnion₂.mp hx
    exact hs.1
  calc
    _ ≤ volume.real (⋃ s ∈ T, A s) := measureReal_mono hsub hfin
    _ ≤ ∑ s ∈ T, volume.real (A s) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ s ∈ T, (volume.real (cube L))^s.card *
        ((s.card : ℝ)*volume.real (Metric.closedBall (0 : Space) ((1+shellDelta)*Real.exp (-t))))^(Fintype.card ι-s.card) := by
      exact Finset.sum_le_sum (fun s _ => rootCover_volume_real s _ L)
    _ = _ := by
      rw [Finset.sum_filter]
      have hh := Finset.sum_powerset_apply_card
        (fun k => if k ≤ packingNumber L ∧ Fintype.card ι ≤ 4*k then
          (volume.real (cube L))^k *
            ((k : ℝ)*volume.real (Metric.closedBall (0 : Space) ((1+shellDelta)*Real.exp (-t))))^(Fintype.card ι-k) else 0)
        (x := (Finset.univ : Finset ι))
      simp only [Finset.powerset_univ, Finset.card_univ, nsmul_eq_mul] at hh
      rw [hh]
      apply Finset.sum_congr rfl
      intro k hk
      split_ifs <;> simp [mul_assoc]

end ContinuumTemperature
end

end OAI
